(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.

From MetaRocq.Common Require Universes.
From Equations Require Import Equations.
Set Equations Transparent.

Ltac rw l := rewrite_strat (topdown l).
Ltac rw_in l H := rewrite_strat (topdown l) in H.


(* TODO move *)
Arguments exist {A P}.
Definition inspect {A} (x : A) : { y : A | x = y } := exist x eq_refl.

Module FMapOrderedType_from_UsualOrderedType (O : UsualOrderedType).
  Import O.
  Definition t := O.t.
  Definition eq : O.t -> O.t -> Prop := O.eq.
  Definition lt : O.t -> O.t -> Prop := O.lt.
  Definition eq_refl : forall x : O.t, eq x x := reflexivity.
  Definition eq_sym : forall x y : O.t, eq x y -> eq y x := fun x y H => symmetry H.

  Lemma eq_trans : forall x y z, O.eq x y -> O.eq y z -> O.eq x z.
  Proof. intros x y z. unfold O.eq. apply transitivity. Qed.
  Lemma lt_trans : forall x y z, O.lt x y -> O.lt y z -> O.lt x z.
  Proof. intros. eapply O.lt_strorder; tea. Qed.

  Lemma lt_not_eq : forall x y : O.t, lt x y -> ~ eq x y.
  Proof.
    intros x y H eq. do 2 red in eq. subst x. now eapply lt_strorder in H.
  Qed.

  Definition compare : forall x y : O.t, Compare lt eq x y.
  Proof.
    intros.
    case_eq (compare x y); intros.
    apply EQ. abstract (destruct (compare_spec x y) => //).
    apply LT. abstract (destruct (compare_spec x y) => //).
    apply GT. abstract (destruct (compare_spec x y) => //).
  Defined.

  Definition eq_dec : forall x y : O.t, {eq x y} + {~ eq x y} := eq_dec.
End FMapOrderedType_from_UsualOrderedType.

Module Type LevelOrderedType.
  Include UsualOrderedType.

  Parameter reflect_eq : ReflectEq t.
  #[local] Existing Instance reflect_eq.
  Parameter eq_leibniz : forall (x y : t), eq x y -> x = y.

  Parameter to_string : t -> string.

End LevelOrderedType.

Module Type FMapOTInterface (E : UsualOrderedType).
  Module OT := FMapOrderedType_from_UsualOrderedType E.
  Include FMapInterface.Sfun OT.
End FMapOTInterface.

Module Type LevelSet_fun (Level : LevelOrderedType).
  Include SWithLeibniz with Module E := Level.
End LevelSet_fun.

Module Type LevelExprItf (Level : LevelOrderedType).
  Include UsualOrderedType with Definition t := (Level.t * nat)%type.
  Parameter eq_leibniz : forall (x y : t), eq x y -> x = y.
End LevelExprItf.

Module Type LevelExprSet_fun (Level : LevelOrderedType) (LevelExpr : LevelExprItf Level).
  Include SWithLeibniz with Module E := LevelExpr.

  Record nonEmptyLevelExprSet
    := { t_set :> t ;
          t_ne  : is_empty t_set = false }.

  (* Parameter map : (LevelExpr.t -> LevelExpr.t) -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet. *)

  (* Parameter map_spec : forall e f u, In e (map f u) <-> exists e0, In e0 u /\ e = (f e0). *)

End LevelExprSet_fun.

Module Type LoopCheckingItf (Level : LevelOrderedType)
  (LevelSet : LevelSet_fun Level)
  (LevelExpr : LevelExprItf Level)
  (LevelExprSet : LevelExprSet_fun Level LevelExpr)
  (LevelMap : FMapOTInterface Level).

  Definition model := LevelMap.t nat.
  Definition valuation := LevelMap.t nat.

  Definition clause : Type := LevelExprSet.nonEmptyLevelExprSet × LevelExpr.t.

  Parameter clauses : Type.
  Parameter clauses_of_list : list clause -> clauses.
  Parameter list_of_clauses : clauses -> list clause.

  Inductive constraint_type := UnivEq | UnivLe.
  Notation constraint := (LevelExprSet.nonEmptyLevelExprSet * constraint_type * LevelExprSet.nonEmptyLevelExprSet).

  Parameter enforce_constraint : forall (cstr : constraint) (cls : clauses), clauses.

  Parameter valid_model : forall (V : LevelSet.t) (U : LevelSet.t) (m : model) (cls : clauses), Type.

  Parameter model_model : forall V U m cls, valid_model V U m cls -> model.

    (* { model_model : model;
      model_of_V :> model_of V model_model;
      model_clauses_conclusions : clauses_conclusions cls ⊂_lset V;
      model_ok :> is_model cls model_model;
      model_extends : model_extension V m model_model;
   }. *)

  Infix "⊂_lset" := LevelSet.Subset (at level 70).

  Parameter enforce_clauses : forall {V U init cls} (m : valid_model V U init cls) (cls' : clauses), option model.

  Parameter loop_on : forall w : LevelSet.t, ~ LevelSet.Empty w -> clauses -> Prop.

  Inductive result (V U : LevelSet.t) (cls : clauses) (m : model) :=
  | Loop (w : LevelSet.t) (hne : ~ LevelSet.Empty w) (islooping : loop_on w hne cls)
  | Model (w : LevelSet.t) (m : valid_model V w m cls) (prf : U ⊂_lset w).

  Parameter init_model : clauses -> model.
  Parameter clauses_levels : clauses -> LevelSet.t.

  Definition infer_result V cls := result V LevelSet.empty cls (init_model cls).

  Parameter infer : forall (cls : clauses), infer_result (clauses_levels cls) cls.

  Parameter print_result : forall {V cls}, infer_result V cls -> string.

  Parameter print_clauses : clauses -> string.

End LoopCheckingItf.

Module LoopChecking
  (* Signature of levels: decidable, ordered type *)
  (Level : LevelOrderedType)
  (LevelSet : LevelSet_fun Level)
  (LevelExpr : LevelExprItf Level)
  (LevelExprSet : LevelExprSet_fun Level LevelExpr)
  (LevelMap : FMapOTInterface Level) <: LoopCheckingItf Level LevelSet LevelExpr LevelExprSet LevelMap.

Definition level (e : LevelExpr.t) : Level.t := fst e.
Definition levels (e : LevelExprSet.t) :=
  LevelExprSet.fold (fun le => LevelSet.add (level le)) e LevelSet.empty.
  Import LevelExprSet (nonEmptyLevelExprSet, t_set, t_ne).


Local Existing Instance Level.reflect_eq.

Module LevelSetFact := WFactsOn Level LevelSet.
Module LevelSetProp := WPropertiesOn Level LevelSet.
Module LevelSetDecide := LevelSetProp.Dec.
Module LevelMapFact := FMapFacts.WProperties_fun LevelMap.OT LevelMap.

Ltac lsets := LevelSetDecide.fsetdec.
Notation "(=_lset)" := LevelSet.Equal (at level 0).
Infix "=_lset" := LevelSet.Equal (at level 30).
Infix "⊂_lset" := LevelSet.Subset (at level 70).
Infix "∪" := LevelSet.union (at level 70).

Definition print_level_nat_map (m : LevelMap.t nat) :=
  let list := LevelMap.elements m in
  print_list (fun '(l, w) => Level.to_string l ^ " -> " ^ string_of_nat w) nl list.

Definition print_lset (l : LevelSet.t) :=
  let list := LevelSet.elements l in
  print_list Level.to_string " " list.

Module LevelExprSetFact := WFactsOn LevelExpr LevelExprSet.
Module LevelExprSetProp := WPropertiesOn LevelExpr LevelExprSet.

(* We have decidable equality w.r.t leibniz equality for sets of levels. *)
#[global, program] Instance levelexprset_reflect : ReflectEq LevelExprSet.t :=
  { eqb := LevelExprSet.equal }.
Next Obligation.
  destruct (LevelExprSet.equal x y) eqn:e; constructor.
  eapply LevelExprSet.equal_spec in e.
  now eapply LevelExprSet.eq_leibniz.
  intros e'.
  subst y.
  pose proof (@LevelExprSetFact.equal_1 x x).
  forward H. reflexivity. congruence.
Qed.

#[global] Instance levelexprset_eq_dec : Classes.EqDec LevelExprSet.t := Classes.eq_dec.

Derive NoConfusion for LevelExprSet.nonEmptyLevelExprSet.

(* We use uip on the is_empty condition *)
#[global, program] Instance nonEmptyLevelExprSet_reflect : ReflectEq nonEmptyLevelExprSet :=
  { eqb x y := eqb x.(t_set) y.(t_set) }.
Next Obligation.
  destruct (eqb_spec (t_set x) (t_set y)); constructor.
  destruct x, y; cbn in *. subst.
  now rewrite (uip t_ne0 t_ne1).
  intros e; subst x; apply H.
  reflexivity.
Qed.

(** This coercion allows to see the non-empty set as a regular [LevelExprSet.t] *)
Coercion t_set : nonEmptyLevelExprSet >-> LevelExprSet.t.
Module LevelExprSetDecide := WDecide (LevelExprSet).
Ltac lesets := LevelExprSetDecide.fsetdec.
Infix "⊂_leset" := LevelExprSet.Subset (at level 70).

Lemma levelset_not_Empty_is_empty s :
  LevelSet.is_empty s = false <-> ~ LevelSet.Empty s.
Proof.
  split.
  - intros H he. red in he. apply negbT in H. unshelve eapply (contraNnot _ H).
    3:exact he. intros ha. now apply LevelSetFact.is_empty_1.
  - intros ne. destruct LevelSet.is_empty eqn:he => //.
    eapply LevelSetFact.is_empty_2 in he. contradiction.
Qed.

Module NonEmptySetFacts.
  #[program] Definition singleton (e : LevelExpr.t) : nonEmptyLevelExprSet
    := {| t_set := LevelExprSet.singleton e |}.
  Next Obligation.
    apply negbTE.
    eapply (contra_notN (P := LevelExprSet.Empty (LevelExprSet.singleton e))).
    apply LevelExprSetFact.is_empty_2. intros ne. red in ne. specialize (ne e). lesets.
  Qed.

  Lemma not_Empty_is_empty s :
    ~ LevelExprSet.Empty s <-> LevelExprSet.is_empty s = false.
  Proof.
    split.
    - intro H. apply not_true_is_false. intro H'.
      apply H. now apply LevelExprSetFact.is_empty_2 in H'.
    - intros H he. red in he. apply negbT in H. unshelve eapply (contraNnot _ H).
      3:exact he. intros ha. now apply LevelExprSetFact.is_empty_1.
  Qed.

  Program Definition add (e : LevelExpr.t) (u : nonEmptyLevelExprSet) : nonEmptyLevelExprSet
    := {| t_set := LevelExprSet.add e u |}.
  Next Obligation.
    apply not_Empty_is_empty; intro H.
    eapply H. eapply LevelExprSet.add_spec.
    left; reflexivity.
  Qed.

  Lemma add_spec e u e' :
    LevelExprSet.In e' (add e u) <-> e' = e \/ LevelExprSet.In e' u.
  Proof.
    apply LevelExprSet.add_spec.
  Qed.

  Definition add_list : list LevelExpr.t -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet
    := List.fold_left (fun u e => add e u).

  Lemma add_list_spec l u e :
    LevelExprSet.In e (add_list l u) <-> In e l \/ LevelExprSet.In e u.
  Proof.
    unfold add_list. rewrite <- fold_left_rev_right.
    etransitivity. 2:{ eapply or_iff_compat_r. etransitivity.
                        2: apply @InA_In_eq with (A:=LevelExpr.t).
                        eapply InA_rev. }
    induction (List.rev l); cbn.
    - split. intuition. intros [H|H]; tas. invs H.
    - split.
      + intro H. apply add_spec in H. destruct H as [H|H].
        * left. now constructor.
        * apply IHl0 in H. destruct H as [H|H]; [left|now right].
          now constructor 2.
      + intros [H|H]. inv H.
        * apply add_spec; now left.
        * apply add_spec; right. apply IHl0. now left.
        * apply add_spec; right. apply IHl0. now right.
  Qed.

  Lemma elements_not_empty {u : nonEmptyLevelExprSet} : LevelExprSet.elements u <> [].
  Proof.
    rewrite -LevelExprSetProp.elements_Empty.
    move/LevelExprSetFact.is_empty_1.
    destruct u as [u1 u2]; cbn in *. congruence.
  Qed.

  Equations to_nonempty_list (u : nonEmptyLevelExprSet) : LevelExpr.t * list LevelExpr.t :=
  | u with inspect (LevelExprSet.elements u) := {
    | exist [] eqel => False_rect _ (elements_not_empty eqel)
    | exist (e :: l) _ => (e, l) }.

  Lemma singleton_to_nonempty_list e : to_nonempty_list (singleton e) = (e, []).
  Proof.
    funelim (to_nonempty_list (singleton e)). bang.
    clear H.
    pose proof (LevelExprSet.singleton_spec e1 e).
    rewrite LevelExprSetFact.elements_iff in H.
    rewrite InA_In_eq in H. rewrite e0 in H.
    destruct H. forward H. now left. noconf H. f_equal.
    pose proof (LevelExprSet.cardinal_spec (LevelExprSet.singleton e1)). rewrite e0 in H. cbn in H.
    rewrite LevelExprSetProp.singleton_cardinal in H.
    destruct l => //.
  Qed.

  Lemma to_nonempty_list_spec u :
    let '(e, u') := to_nonempty_list u in
    e :: u' = LevelExprSet.elements u.
  Proof.
    funelim (to_nonempty_list u). bang. now rewrite e0.
  Qed.

  Lemma to_nonempty_list_spec' u :
    (to_nonempty_list u).1 :: (to_nonempty_list u).2 = LevelExprSet.elements u.
  Proof.
    pose proof (to_nonempty_list_spec u).
    now destruct (to_nonempty_list u).
  Qed.

  Lemma In_to_nonempty_list (u : nonEmptyLevelExprSet) (e : LevelExpr.t) :
    LevelExprSet.In e u
    <-> e = (to_nonempty_list u).1 \/ In e (to_nonempty_list u).2.
  Proof.
    etransitivity. symmetry. apply LevelExprSet.elements_spec1.
    pose proof (to_nonempty_list_spec' u) as H.
    destruct (to_nonempty_list u) as [e' l]; cbn in *.
    rewrite <- H; clear. etransitivity. apply InA_cons.
    eapply or_iff_compat_l. apply InA_In_eq.
  Qed.

  Lemma In_to_nonempty_list_rev (u : nonEmptyLevelExprSet) (e : LevelExpr.t) :
    LevelExprSet.In e u
    <-> e = (to_nonempty_list u).1 \/ In e (List.rev (to_nonempty_list u).2).
  Proof.
    etransitivity. eapply In_to_nonempty_list.
    apply or_iff_compat_l. apply in_rev.
  Qed.

  Definition map (f : LevelExpr.t -> LevelExpr.t) (u : nonEmptyLevelExprSet) : nonEmptyLevelExprSet :=
    let '(e, l) := to_nonempty_list u in
    add_list (List.map f l) (singleton (f e)).

  Lemma map_spec f u e :
    LevelExprSet.In e (map f u) <-> exists e0, LevelExprSet.In e0 u /\ e = (f e0).
  Proof.
    unfold map. symmetry. etransitivity.
    { eapply iff_ex; intro. eapply and_iff_compat_r. eapply In_to_nonempty_list. }
    destruct (to_nonempty_list u) as [e' l]; cbn in *.
    symmetry. etransitivity. eapply add_list_spec.
    etransitivity. eapply or_iff_compat_l. apply LevelExprSet.singleton_spec.
    etransitivity. eapply or_iff_compat_r.
    apply in_map_iff. clear u. split.
    - intros [[e0 []]|H].
      + exists e0. split. right; tas. congruence.
      + exists e'. split; tas. left; reflexivity.
    - intros [xx [[H|H] ?]].
      + right. congruence.
      + left. exists xx. split; tas; congruence.
  Qed.

  Program Definition non_empty_union (u v : nonEmptyLevelExprSet) : nonEmptyLevelExprSet :=
    {| t_set := LevelExprSet.union u v |}.
  Next Obligation.
    apply not_Empty_is_empty; intro H.
    assert (HH: LevelExprSet.Empty u). {
      intros x Hx. apply (H x).
      eapply LevelExprSet.union_spec. now left. }
    apply LevelExprSetFact.is_empty_1 in HH.
    rewrite t_ne in HH; discriminate.
  Qed.


  Lemma eq_univ (u v : nonEmptyLevelExprSet) :
    u = v :> LevelExprSet.t -> u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; cbn. intros X; destruct X.
    now rewrite (uip_bool _ _ u2 v2).
  Qed.

  Lemma eq_univ' (u v : nonEmptyLevelExprSet) :
    LevelExprSet.Equal u v -> u = v.
  Proof.
    intro H. now apply eq_univ, LevelExprSet.eq_leibniz.
  Qed.

  Lemma eq_univ'' (u v : nonEmptyLevelExprSet) :
    LevelExprSet.elements u = LevelExprSet.elements v -> u = v.
  Proof.
    intro H. apply eq_univ.
    destruct u as [u1 u2], v as [v1 v2]; cbn in *; clear u2 v2.
    eapply LevelExprSet.eq_leibniz. red.
    intros x. rewrite -!LevelExprSet.elements_spec1 H //.
  Qed.

  Lemma univ_expr_eqb_true_iff (u v : nonEmptyLevelExprSet) :
    LevelExprSet.equal u v <-> u = v.
  Proof.
    split.
    - intros.
      apply eq_univ'. now apply LevelExprSet.equal_spec.
    - intros ->. now apply LevelExprSet.equal_spec.
  Qed.

  Lemma univ_expr_eqb_comm (u v : nonEmptyLevelExprSet) :
    LevelExprSet.equal u v <-> LevelExprSet.equal v u.
  Proof.
    transitivity (u = v). 2: transitivity (v = u).
    - apply univ_expr_eqb_true_iff.
    - split; apply eq_sym.
    - split; apply univ_expr_eqb_true_iff.
  Qed.


  Lemma LevelExprSet_for_all_false f u :
    LevelExprSet.for_all f u = false -> LevelExprSet.exists_ (negb ∘ f) u.
  Proof.
    intro H. rewrite LevelExprSetFact.exists_b.
    rewrite LevelExprSetFact.for_all_b in H.
    all: try now intros x y [].
    induction (LevelExprSet.elements u); cbn in *; [discriminate|].
    apply andb_false_iff in H; apply orb_true_iff; destruct H as [H|H].
    left; now rewrite H.
    right; now rewrite IHl.
  Qed.

  Lemma LevelExprSet_For_all_exprs (P : LevelExpr.t -> Prop) (u : nonEmptyLevelExprSet)
    : LevelExprSet.For_all P u
      <-> P (to_nonempty_list u).1 /\ Forall P (to_nonempty_list u).2.
  Proof.
    etransitivity.
    - eapply iff_forall; intro e. eapply imp_iff_compat_r.
      apply In_to_nonempty_list.
    - cbn; split.
      + intro H. split. apply H. now left.
        apply Forall_forall. intros x H0.  apply H; now right.
      + intros [H1 H2] e [He|He]. subst e; tas.
        eapply Forall_forall in H2; tea.
  Qed.

  Lemma add_comm {le le' e} : add le (add le' e) = add le' (add le e).
  Proof.
    apply eq_univ'. intros x.
    rewrite !LevelExprSet.add_spec. firstorder.
  Qed.

  #[program]
  Definition univ_union (prems prems' : nonEmptyLevelExprSet) : nonEmptyLevelExprSet :=
    {| t_set := LevelExprSet.union prems prems' |}.
  Next Obligation.
    destruct prems, prems'; cbn.
    destruct (LevelExprSet.is_empty (LevelExprSet.union _ _)) eqn:ise => //.
    eapply LevelExprSetFact.is_empty_2 in ise.
    eapply not_Empty_is_empty in t_ne0, t_ne1.
    destruct t_ne0. lesets.
  Qed.

  Lemma univ_union_spec u u' l :
    LevelExprSet.In l (univ_union u u') <->
    LevelExprSet.In l u \/ LevelExprSet.In l u'.
  Proof.
    destruct u, u'; unfold univ_union; cbn.
    apply LevelExprSet.union_spec.
  Qed.

  Lemma univ_union_add_singleton u le : univ_union u (singleton le) = add le u.
  Proof.
    apply eq_univ'.
    intros x. rewrite univ_union_spec LevelExprSet.singleton_spec add_spec.
    intuition auto.
  Qed.

  Lemma univ_union_comm {u u'} : univ_union u u' = univ_union u' u.
  Proof.
    apply eq_univ'.
    intros x. rewrite !univ_union_spec.
    intuition auto.
  Qed.

  Lemma univ_union_add_distr {le u u'} : univ_union (add le u) u' = add le (univ_union u u').
  Proof.
    apply eq_univ'.
    intros x. rewrite !univ_union_spec !add_spec !univ_union_spec.
    intuition auto.
  Qed.


End NonEmptySetFacts.
Import NonEmptySetFacts.

Notation univ := nonEmptyLevelExprSet.

Definition clause : Type := univ × LevelExpr.t.

Module Clause.
  Definition t := clause.

  Definition eq : t -> t -> Prop := eq.

  Definition eq_equiv : RelationClasses.Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | lt_clause1 l e e' : LevelExpr.lt e e' -> lt_ (l, e) (l, e')
  | lt_clause2 l l' b b' : LevelExprSet.lt l.(t_set) l'.(t_set) -> lt_ (l, b) (l', b').

  Definition lt := lt_.

  Global Instance lt_strorder : RelationClasses.StrictOrder lt.
  Proof.
    constructor.
    - intros x X; inversion X; subst. now eapply LevelExpr.lt_strorder in H1.
      eapply LevelExprSet.lt_strorder; eassumption.
    - intros x y z X1 X2; invs X1; invs X2; constructor; tea.
      etransitivity; tea.
      etransitivity; tea.
  Qed.

  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
    intros x x' H1 y y' H2. unfold lt. subst. reflexivity.
  Qed.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | (l1, b1), (l2, b2) =>
      match LevelExprSet.compare l1.(t_set) l2.(t_set) with
      | Eq => LevelExpr.compare b1 b2
      | x => x
      end
    end.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [? ?] [? ?]; cbn; repeat constructor.
    destruct (LevelExprSet.compare_spec n n0); repeat constructor; tas.
    eapply LevelExprSet.eq_leibniz in H. apply NonEmptySetFacts.eq_univ in H.
    subst. cbn in *.
    destruct (LevelExpr.compare_spec t0 t1); repeat constructor; tas. now subst.
  Qed.

  Global Instance reflect_t : ReflectEq t := reflect_prod _ _ .

  Definition eq_dec : forall (l1 l2 : t), {l1 = l2} + {l1 <> l2} := Classes.eq_dec.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.
End Clause.

Module Clauses := MSetAVL.Make Clause.
Module ClausesFact := WFactsOn Clause Clauses.
Module ClausesProp := WPropertiesOn Clause Clauses.
Module ClausesDecide := WDecide (Clauses).
Ltac clsets := ClausesDecide.fsetdec.

Definition clauses := Clauses.t.

Lemma filter_add {p x s} : Clauses.Equal (Clauses.filter p (Clauses.add x s)) (if p x then Clauses.add x (Clauses.filter p s) else Clauses.filter p s).
Proof.
  intros i.
  rewrite Clauses.filter_spec.
  destruct (eqb_spec i x); subst;
  destruct (p x) eqn:px; rewrite !Clauses.add_spec !Clauses.filter_spec; intuition auto || congruence.
Qed.

Local Instance proper_fold_transpose {A} (f : Clauses.elt -> A -> A) :
  transpose eq f ->
  Proper (Clauses.Equal ==> eq ==> eq) (Clauses.fold f).
Proof.
  intros hf s s' Hss' x ? <-.
  eapply ClausesProp.fold_equal; tc; tea.
Qed.
Existing Class transpose.

Lemma clauses_fold_filter {A} (f : Clauses.elt -> A -> A) (p : Clauses.elt -> bool) cls acc :
  transpose Logic.eq f ->
  Clauses.fold f (Clauses.filter p cls) acc =
  Clauses.fold (fun elt acc => if p elt then f elt acc else acc) cls acc.
Proof.
  intros hf.
  symmetry. eapply ClausesProp.fold_rec_bis.
  - intros s s' a eq. intros ->.
    eapply ClausesProp.fold_equal; tc. auto.
    intros x.
    rewrite !Clauses.filter_spec.
    now rewrite eq.
  - now cbn.
  - intros.
    rewrite H1.
    rewrite filter_add.
    destruct (p x) eqn:px => //.
    rewrite ClausesProp.fold_add //.
    rewrite Clauses.filter_spec. intuition auto.
Qed.

Definition levelexpr_level : LevelExpr.t -> Level.t := fst.
Coercion levelexpr_level : LevelExpr.t >-> Level.t.
Extraction Inline levelexpr_level.

Definition strict_subset (s s' : LevelSet.t) :=
  LevelSet.Subset s s' /\ ~ LevelSet.Equal s s'.

Lemma strict_subset_incl (x y z : LevelSet.t) : LevelSet.Subset x y -> strict_subset y z -> strict_subset x z.
Proof.
  intros hs []. split => //. lsets.
  intros heq. apply H0. lsets.
Qed.

Lemma strict_subset_cardinal s s' : strict_subset s s' -> LevelSet.cardinal s < LevelSet.cardinal s'.
Proof.
  intros [].
  assert (LevelSet.cardinal s <> LevelSet.cardinal s').
  { intros heq. apply H0.
    intros x. split; intros. now apply H.
    destruct (LevelSet.mem x s) eqn:hin.
    eapply LevelSet.mem_spec in hin.
    auto. eapply LevelSetProp.FM.not_mem_iff in hin.
    exfalso.
    eapply LevelSetProp.subset_cardinal_lt in hin; tea.
    lia. }
  enough (LevelSet.cardinal s <= LevelSet.cardinal s') by lia.
  now eapply LevelSetProp.subset_cardinal.
Qed.

Definition premise (cl : clause) := fst cl.
Definition concl (cl : clause) := snd cl.
Extraction Inline premise concl.

Definition clause_levels cl :=
  LevelSet.union (levels (premise cl)) (LevelSet.singleton (levelexpr_level (concl cl))).

Definition clauses_levels (cls : clauses) : LevelSet.t :=
  Clauses.fold (fun cl acc => LevelSet.union (clause_levels cl) acc) cls LevelSet.empty.

Lemma Clauses_In_elements l s :
  In l (Clauses.elements s) <-> Clauses.In l s.
Proof.
  rewrite ClausesFact.elements_iff.
  now rewrite InA_In_eq.
Qed.

Lemma clauses_levels_spec_aux l cls acc :
  LevelSet.In l (Clauses.fold (fun cl acc => LevelSet.union (clause_levels cl) acc) cls acc) <->
  (exists cl, Clauses.In cl cls /\ LevelSet.In l (clause_levels cl)) \/ LevelSet.In l acc.
Proof.
  eapply ClausesProp.fold_rec.
  - intros.
    intuition auto. destruct H1 as [k [hin hl]]. clsets.
  - intros x a s' s'' hin nin hadd ih.
    rewrite LevelSet.union_spec.
    split.
    * intros [hin'|].
      left. exists x. split => //.
      apply hadd. now left.
      apply ih in H.
      intuition auto.
      left. destruct H0 as [k Hk]. exists k. intuition auto. apply hadd. now right.
    * intros [[k [ins'' ?]]|inacc].
      eapply hadd in ins''. destruct ins''; subst.
      + now left.
      + right. apply ih. now left; exists k.
      + right. intuition auto.
Qed.

Lemma clauses_levels_spec l cls :
  LevelSet.In l (clauses_levels cls) <->
  exists cl, Clauses.In cl cls /\ LevelSet.In l (clause_levels cl).
Proof.
  unfold clauses_levels.
  rewrite clauses_levels_spec_aux.
  intuition auto. lsets.
Qed.

Instance clauses_levels_proper : Proper (Clauses.Equal ==> LevelSet.Equal) clauses_levels.
Proof.
  intros cl cl' eq x.
  rewrite !clauses_levels_spec.
  now setoid_rewrite eq.
Qed.

Lemma clause_levels_spec l cl :
  LevelSet.In l (clause_levels cl) <->
  LevelSet.In l (levels (premise cl)) \/ l = levelexpr_level (concl cl).
Proof.
  unfold clause_levels.
  now rewrite LevelSet.union_spec LevelSet.singleton_spec.
Qed.

Definition clause_conclusion cl := levelexpr_level (concl cl).

Definition model := LevelMap.t nat.

Definition level_value (m : model) (level : Level.t) : option nat := LevelMap.find level m.

Definition levelexpr_value (m : model) (atom : LevelExpr.t) :=
  level_value m (levelexpr_level atom).

Extraction Inline levelexpr_value.

Definition min_atom_value (m : model) (atom : LevelExpr.t) : option Z :=
  let '(l, k) := atom in
  match level_value m l with
  | None => None
  | Some val => Some (Z.of_nat val - Z.of_nat k)%Z
  end.

Definition option_map2 {A} (f : A -> A -> A) (o o' : option A) : option A :=
  match o, o' with
  | Some x, Some y => Some (f x y)
  | None, Some _
  | Some _, None
  | None, None => None
  end.

Definition min_premise (m : model) (l : nonEmptyLevelExprSet) : option Z :=
  let (hd, tl) := NonEmptySetFacts.to_nonempty_list l in
  fold_left (fun min atom => option_map2 Z.min (min_atom_value m atom) min) tl (min_atom_value m hd).

Definition satisfiable_atom (m : model) (atom : Level.t * nat) : bool :=
  let '(l, k) := atom in
  match level_value m l with
  | Some val => k <=? val
  | None => false
  end.

Definition satisfiable_premise (m : model) (l : nonEmptyLevelExprSet) :=
  LevelExprSet.for_all (satisfiable_atom m) l.

(* Definition valid_clause (m : model) (cl : clause) := *)
  (* implb (satisfiable_premise m (premise cl)) (satisfiable_atom m (concl cl)). *)
Definition level_value_above m l k :=
  match level_value m l with
  | Some val => k <=? val
  | None => false
  end.

Definition valid_clause (m : model) (cl : clause) :=
  let k0 := min_premise m (premise cl) in
  match k0 with
  | None => true
  | Some k0 =>
    let (l, k) := concl cl in
    (k0 <? 0)%Z || level_value_above m l (k + Z.to_nat k0)
  end.

Definition is_model (cls : clauses) (m : model) : bool :=
  Clauses.for_all (valid_clause m) cls.

Inductive update_result :=
  | VacuouslyTrue
  | Holds
  | DoesntHold (wm : LevelSet.t × model).

Definition update_model (m : model) l v : model := LevelMap.add l v m.

Definition update_value (m : model) (cl : clause) : option model :=
  let k0 := min_premise m (premise cl) in
  match k0 with
  | None => None
  | Some k0 =>
    if (k0 <? 0)%Z then None else
    let (l, k) := concl cl in
    (* Does the conclusion also hold?
        We optimize a bit here, rather than adding k0 in a second stage,
        we do it already while checking the clause. In the paper, a second
        pass computes this.
      *)
    if level_value_above m l (k + Z.to_nat k0) then None
    else Some (update_model m l (k + Z.to_nat k0))
  end.

Definition check_clause_model cl '(modified, m) :=
    match update_value m cl with
  | None => (modified, m)
  | Some m => (clause_conclusion cl :: modified, m)
  end.

Definition check_model_aux (cls : clauses) (wm : list Level.t × model) : list Level.t × model :=
  Clauses.fold check_clause_model cls wm.

(* If check_model = None then we have a model of all clauses,
  othewise, we return Some (W', m') where W ⊂ W' and the model has
  been updated for at least one atom l ∈ W'. *)
Definition check_model (cls : clauses) (wm : LevelSet.t × model) : option (LevelSet.t × model) :=
  let '(modified, m) := check_model_aux cls ([], wm.2) in
  match modified return option (LevelSet.t × model) with
  | [] => None
  | l => Some ((LevelSet.union (LevelSetProp.of_list l) wm.1), m)
  end.

Infix "=m" := LevelMap.Equal (at level 50).

Definition strict_update m '(prems, (l, k)) m' :=
  exists v,
  [/\ min_premise m prems = Some v, (0 <= v)%Z, ~~ level_value_above m l (k + Z.to_nat v) &
  m' =m (LevelMap.add l (k + Z.to_nat v) m)].

Inductive strictly_updates cls : LevelSet.t -> model -> model -> Prop :=
| update_one m cl m' : Clauses.In cl cls ->
  strict_update m cl m' -> strictly_updates cls (LevelSet.singleton (clause_conclusion cl)) m m'
| update_trans {ls ls' m m' m''} :
  strictly_updates cls ls m m' ->
  strictly_updates cls ls' m' m'' ->
  strictly_updates cls (LevelSet.union ls ls') m m''.

Lemma strictly_updates_step cls w m m' m'' :
  strictly_updates cls w m m' ->
  forall cl, Clauses.In cl cls -> strict_update m' cl m'' ->
  strictly_updates cls (LevelSet.add (clause_conclusion cl) w) m m''.
Proof.
  induction 1.
  - intros.
    replace (LevelSet.add (clause_conclusion cl0) (LevelSet.singleton (clause_conclusion cl)))
      with (LevelSet.union (LevelSet.singleton (clause_conclusion cl)) (LevelSet.singleton (clause_conclusion cl0))).
    eapply update_trans; eapply update_one; tea.
    eapply LevelSet.eq_leibniz. red. lsets.
  - intros.
    specialize (IHstrictly_updates2 _ H1 H2).
    replace (LevelSet.add (clause_conclusion cl) (LevelSet.union ls ls'))
      with (LevelSet.union ls (LevelSet.add (clause_conclusion cl) ls')).
    eapply update_trans; tea.
    eapply LevelSet.eq_leibniz. red. lsets.
Qed.

Lemma strictly_updates_weaken cls w cls' :
  Clauses.Subset cls cls' ->
  forall m m', strictly_updates cls w m m' -> strictly_updates cls' w m m'.
Proof.
  intros hcls m m'.
  induction 1. constructor => //. now eapply hcls.
  econstructor 2; tea.
Qed.

Lemma strictly_updates_W_trans cls m w m' cl m'' :
  strictly_updates cls w m m' ->
  strict_update m' cl m'' ->
  strictly_updates (Clauses.add cl cls) (LevelSet.add (clause_conclusion cl) w) m m''.
Proof.
  intros updW su.
  destruct cl as [prems [concl k]].
  eapply strictly_updates_step; tea.
  - eapply strictly_updates_weaken; tea. clsets.
  - rewrite Clauses.add_spec. left; reflexivity.
Qed.

#[local] Instance Clauses_For_All_proper : Proper (eq ==> Clauses.Equal ==> iff) Clauses.For_all.
Proof.
  intros x y -> cl cl' eqcl.
  unfold Clauses.For_all. now setoid_rewrite eqcl.
Qed.

#[local] Instance Clauses_for_all_proper : Proper (eq ==> Clauses.Equal ==> eq) Clauses.for_all.
Proof.
  intros x y -> cl cl' eqcl.
  apply iff_is_true_eq_bool.
  rewrite /is_true -!ClausesFact.for_all_iff. now rewrite eqcl.
Qed.

#[local] Instance is_model_proper : Proper (Clauses.Equal ==> eq ==> eq) is_model.
Proof.
  intros cl cl' eqcl x y ->. unfold is_model. now rewrite eqcl.
Qed.


Definition equal_model (m m' : model) := LevelMap.Equal m m'.

#[local] Instance equal_model_equiv : Equivalence equal_model.
Proof. unfold equal_model.
  split; try econstructor; eauto.
  red. intros. now symmetry.
  red; intros. now transitivity y.
Qed.


#[local] Instance level_value_proper : Proper (equal_model ==> eq ==> eq) level_value.
Proof.
  intros x y eqm l ? <-. unfold level_value.
  unfold equal_model in eqm.
  destruct LevelMap.find eqn:hl.
  - eapply LevelMap.find_2 in hl.
    rewrite eqm in hl.
    eapply LevelMap.find_1 in hl. now rewrite hl.
  - eapply LevelMapFact.F.not_find_in_iff in hl.
    rewrite eqm in hl.
    eapply LevelMapFact.F.not_find_in_iff in hl.
    now rewrite hl.
Qed.

#[local] Instance min_atom_value_proper : Proper (LevelMap.Equal ==> eq ==> eq) min_atom_value.
Proof.
  intros m m' eqm ? ? ->. unfold min_atom_value.
  destruct y => //.
  now rewrite eqm.
Qed.

#[local] Instance fold_left_ext {A B} : Proper (`=2` ==> eq ==> eq ==> eq) (@fold_left A B).
Proof.
  intros f g hfg ? ? -> ? ? ->.
  induction y in y0 |- *; cbn; auto. now rewrite (hfg y0 a).
Qed.

#[local] Instance min_premise_proper : Proper (LevelMap.Equal ==> eq ==> eq) min_premise.
Proof.
  intros m m' eq ? ? ->.
  unfold min_premise.
  destruct to_nonempty_list.
  now setoid_rewrite eq.
Qed.

#[local] Instance update_model_proper : Proper (LevelMap.Equal ==> eq ==> eq ==> LevelMap.Equal) update_model.
Proof.
  intros m m' hm ? ? -> ? ? ->.
  unfold update_model.
  now rewrite hm.
Qed.

#[local] Instance level_value_above_proper : Proper (LevelMap.Equal ==> eq ==> eq ==> eq) level_value_above.
Proof.
  intros m m' hm ? ? -> ? ? ->.
  unfold level_value_above.
  now rewrite hm.
Qed.

#[local] Instance check_model_aux_proper : Proper (Clauses.Equal ==> eq ==> eq) check_model_aux.
Proof.
Admitted.

#[local] Instance check_model_proper : Proper (Clauses.Equal ==> eq ==> eq) check_model.
Proof.
  intros cls cls' eq.
  intros wm wm' ->.
  unfold check_model.
  destruct (check_model_aux cls _) eqn:eqc.
  destruct (check_model_aux cls' _) eqn:eqc' => //.
  pose proof (check_model_aux_proper cls cls' eq ([], wm'.2) _ eq_refl).
  rewrite eqc eqc' in H. noconf H.
  destruct l => //.
Qed.

Instance strictly_updates_proper : Proper (Clauses.Equal ==> LevelSet.Equal ==> LevelMap.Equal ==> LevelMap.Equal ==> iff) strictly_updates.
Proof.
  intros ? ? H ? ? H' ? ? H'' ? ? H'''.
  eapply LevelSet.eq_leibniz in H'. subst y0.
  split.
  induction 1 in y, H, y1, H'', y2, H'''|- * ; [econstructor 1|econstructor 2]; eauto.
  now rewrite <- H. move: H1; unfold strict_update. destruct cl as [premse []].
  intros [v []]; exists v; split;
  try setoid_rewrite <- H;
  try setoid_rewrite <- H'';
  try setoid_rewrite <- H'''; firstorder.
  eapply IHstrictly_updates1; firstorder. firstorder.
  induction 1 in x, H, x1, H'', x2, H'''|- * ; [econstructor 1|econstructor 2]; eauto.
  now rewrite H. move: H1; unfold strict_update. destruct cl as [premse []].
  intros [v []]; exists v; split;
  try setoid_rewrite H;
  try setoid_rewrite H'';
  try setoid_rewrite H'''; firstorder.
  eapply IHstrictly_updates1; firstorder. firstorder.
Qed.

Lemma update_value_valid {m cl} :
  match update_value m cl with
  | None => valid_clause m cl
  | Some _ => ~~ valid_clause m cl
  end.
Proof.
  unfold update_value, valid_clause.
  destruct cl as [prem [l k]]; cbn.
  destruct min_premise => //.
  destruct Z.ltb;
  unfold level_value_above;
  destruct level_value => //.
  destruct Nat.leb => //.
Qed.

Lemma check_clause_model_spec {cl w m w' m'} :
  check_clause_model cl (w, m) = (w', m') ->
  (w = w' -> m = m' /\ valid_clause m cl) /\
  (w <> w' -> w' = clause_conclusion cl :: w /\
    strictly_updates (Clauses.singleton cl) (LevelSet.singleton (clause_conclusion cl)) m m').
Proof.
  unfold check_clause_model.
  destruct update_value eqn:upd; revgoals.
  * intros [= <- <-]. split => //. split => //.
    move: (@update_value_valid m cl). now rewrite upd.
  * intros [= <- <-]. split => //.
    + intros. eapply (f_equal (@List.length _)) in H. cbn in H; lia.
    + intros _. split => //. constructor. clsets. unfold strict_update.
      move: upd. unfold update_value.
      destruct cl as [prems [concl k]]. cbn.
      destruct min_premise => //.
      elim: Z.ltb_spec => // leq.
      destruct level_value_above eqn:hl => //.
      intros [= <-].
      exists z. split => //. rewrite hl. split => //.
Qed.

Derive Signature for InA.

Lemma check_model_aux_spec {cls w m w' m'} :
  check_model_aux cls (w, m) = (w', m') ->
  (w = w' -> m = m' /\ is_model cls m) /\
  (w <> w' -> exists pref, w' = pref ++ w /\ strictly_updates cls (LevelSetProp.of_list pref) m m').
Proof.
  rewrite /check_model_aux /is_model.
  revert w' m'.
  eapply ClausesProp.fold_rec.
  - intros s' he w' m' [= <- <-]. split => //. split => //.
    eapply Clauses.for_all_spec. tc. intros x hin. now apply he in hin.
  - clear. intros x [w'' m''] s' s'' inx nins' hadd ih w' m' cl.
    specialize (ih _ _ eq_refl) as[].
    split; intros; subst.
    + eapply check_clause_model_spec in cl as [].
      destruct (eqb_spec w' w'').
      { subst w''. specialize (H eq_refl) as []. specialize (H1 eq_refl) as []. split => //. congruence.
        eapply Clauses.for_all_spec in H3. eapply Clauses.for_all_spec. all:tc.
        intros ? hin. eapply hadd in hin as []; subst; firstorder. }
      forward H0 by auto. forward H2 by auto.
      destruct H0 as [pref [-> su]].
      destruct pref; cbn in *; try congruence.
      destruct H2. eapply (f_equal (@List.length _)) in H0; cbn in H0. rewrite length_app in H0. lia.
    + eapply check_clause_model_spec in cl as [].
      destruct (eqb_spec w w'').
      { subst w''. specialize (H eq_refl) as []. subst m''.
        destruct (eqb_spec w w'); subst; try congruence.
        specialize (H3 H) as []. subst w'. exists [clause_conclusion x]. split => //.
        replace (LevelSetProp.of_list [clause_conclusion x]) with (LevelSet.singleton (clause_conclusion x)).
        eapply ClausesProp.Add_Equal in hadd. rewrite hadd. eapply strictly_updates_weaken; tea. clsets.
        eapply LevelSet.eq_leibniz. red. intros ?. rewrite LevelSetProp.of_list_1. firstorder. constructor.
        rewrite LevelSet.singleton_spec in H3. firstorder. depelim H3. subst. lsets. depelim H3. }
      specialize (H0 H4).
      destruct (eqb_spec w'' w'); subst.
      { specialize (H2 eq_refl) as []; subst m''.
        destruct H0 as [pref []]. subst w'. exists pref; split => //.
        eapply strictly_updates_weaken; tea. intros ? ?. eapply hadd. clsets. }
      forward H3 by auto. destruct H3 as [->].
      destruct H0 as [pref [-> su]]. eexists (clause_conclusion x :: pref); split => //.
      replace (LevelSetProp.of_list (clause_conclusion x :: pref)) with (LevelSet.union (LevelSetProp.of_list pref) (LevelSet.singleton (clause_conclusion x))).
      eapply (strictly_updates_weaken _ _ s'') in su; tea; try firstorder.
      eapply (strictly_updates_weaken _ _ s'') in H3; tea; try firstorder.
      2:{ intros ?; rewrite Clauses.singleton_spec. intros ->. now apply hadd. }
      exact: update_trans _ su H3.
      apply LevelSet.eq_leibniz. intros ?. cbn. lsets.
Qed.

Lemma check_model_spec {cls w m w' m'} :
  check_model cls (w, m) = Some (w', m') ->
  exists w'', strictly_updates cls w'' m m' /\ w' = LevelSet.union w w''.
Proof.
  unfold check_model.
  destruct check_model_aux eqn:cm.
  apply check_model_aux_spec in cm as [].
  destruct l => //. forward H0. auto with datatypes.
  intros [= <- <-]. destruct H0 as [pref [heq su]].
  rewrite app_nil_r in heq. subst pref.
  exists (LevelSetProp.of_list (t :: l)). split => //.
  eapply LevelSet.eq_leibniz. intros ?. cbn. lsets.
Qed.


Lemma strict_update_invalid m cl m' : strict_update m cl m' -> ~~ valid_clause m cl.
Proof.
  destruct cl as [prems [concl k]].
  cbn.
  intros [v [him hlt hna heq]].
  rewrite /valid_clause. rewrite him //=.
  elim: Z.ltb_spec => //. lia.
Qed.

Lemma strictly_updates_invalid cls w m m' : strictly_updates cls w m m' -> ~~ is_model cls m.
Proof.
  induction 1.
  - eapply strict_update_invalid in H0.
    apply/negbT. unfold is_model.
    destruct Clauses.for_all eqn:fa => //.
    eapply Clauses.for_all_spec in fa; tc. eapply fa in H.
    now rewrite H in H0.
  - auto.
Qed.

Lemma check_model_None {cls acc} :
  check_model cls acc = None <-> is_model cls acc.2.
Proof.
  unfold check_model.
  destruct check_model_aux eqn:cm.
  apply check_model_aux_spec in cm as [ne ex].
  destruct l => //. split => // _. now specialize (ne eq_refl) as [].
  split => //. forward ex by auto with datatypes. destruct ex as [pref [eq su]].
  rewrite app_nil_r in eq; subst pref.
  intros ism. eapply strictly_updates_invalid in su.
  now rewrite ism in su.
Qed.

Lemma check_model_updates_spec {cls w init_model m w' m'} :
  check_model cls (w, m) = Some (w', m') ->
  forall cls', strictly_updates cls' w init_model m ->
  strictly_updates (Clauses.union cls cls') w' init_model m' /\ w ⊂_lset w'.
Proof.
  move/check_model_spec => [w'' [su ->]].
  intros cls' su'. split.
  eapply update_trans; eapply strictly_updates_weaken; tea; clsets. lsets.
Qed.

Lemma strictly_updates_non_empty {cls W m m'} :
  strictly_updates cls W m m' -> ~ LevelSet.Empty W.
Proof.
  induction 1.
  - intros he. specialize (he (clause_conclusion cl)). lsets.
  - intros he. apply IHstrictly_updates2. lsets.
Qed.

Lemma strictly_updates_non_empty_map {cls W m m'} :
  strictly_updates cls W m m' -> ~ LevelMap.Empty m'.
Proof.
  induction 1.
  - intros he. specialize (he (clause_conclusion cl)).
    destruct cl as [prems [concl k]].
    destruct H0 as [? [? ? ? heq]].
    setoid_rewrite heq in he. eapply (he (k + Z.to_nat x)); cbn.
    rewrite LevelMapFact.F.add_mapsto_iff. firstorder.
  - intros he. now apply IHstrictly_updates2.
Qed.

Definition clauses_conclusions (cls : clauses) : LevelSet.t :=
  Clauses.fold (fun cl acc => LevelSet.add (level (concl cl)) acc) cls LevelSet.empty.

Lemma clauses_conclusions_spec a cls :
  LevelSet.In a (clauses_conclusions cls) <->
  exists cl, Clauses.In cl cls /\ level (concl cl) = a.
Proof.
  unfold clauses_conclusions.
  eapply ClausesProp.fold_rec; clear.
  - move=> s' he /=. rewrite LevelSetFact.empty_iff.
    firstorder auto.
  - move=> cl ls cls' cls'' hin hnin hadd ih.
    rewrite LevelSet.add_spec. firstorder eauto.
    specialize (H0 x). cbn in H0.
    apply hadd in H1. firstorder eauto.
    subst. left. now destruct x.
Qed.

Lemma strictly_updates_incl {cls W m m'} :
  strictly_updates cls W m m' -> W ⊂_lset clauses_conclusions cls.
Proof.
  induction 1.
  - intros x. rewrite clauses_conclusions_spec. firstorder. exists cl.
    eapply LevelSet.singleton_spec in H1; red in H1; subst. split => //.
  - lsets.
Qed.

Lemma check_model_subset {cls v} :
  forall w' v', check_model cls v = Some (w', v') -> ~ LevelSet.Empty w'.
Proof.
  intros w' v'.
  move/check_model_spec => [w'' [su ->]].
  eapply strictly_updates_non_empty in su. intros em. apply su. lsets.
Qed.

Definition premise_restricted_to W cl :=
  LevelSet.subset (levels (premise cl)) W.

Definition clause_restricted_to W cl :=
  LevelSet.subset (levels (premise cl)) W &&
  LevelSet.mem (level (concl cl)) W.

Definition restrict_clauses (cls : clauses) (W : LevelSet.t) :=
  Clauses.filter (clause_restricted_to W) cls.

Lemma in_restrict_clauses (cls : clauses) (concls : LevelSet.t) cl :
  Clauses.In cl (restrict_clauses cls concls) <->
  [/\ LevelSet.In (level (concl cl)) concls,
    LevelSet.Subset (levels (premise cl)) concls &
    Clauses.In cl cls].
Proof.
  unfold restrict_clauses.
  rewrite Clauses.filter_spec.
  destruct cl. cbn.
  rewrite andb_true_iff LevelSet.subset_spec LevelSet.mem_spec.
  firstorder auto.
Qed.

Lemma restrict_clauses_subset (cls : clauses) (concls : LevelSet.t) : Clauses.Subset (restrict_clauses cls concls) cls.
Proof.
  intros x; rewrite in_restrict_clauses; now intros [].
Qed.

Definition clauses_with_concl (cls : clauses) (concl : LevelSet.t) :=
  Clauses.filter (fun '(prem, concla) => LevelSet.mem (level concla) concl) cls.

Lemma in_clauses_with_concl (cls : clauses) (concls : LevelSet.t) cl :
  Clauses.In cl (clauses_with_concl cls concls) <->
  LevelSet.In (level (concl cl)) concls /\ Clauses.In cl cls.
Proof.
  unfold clauses_with_concl.
  rewrite Clauses.filter_spec.
  destruct cl. rewrite LevelSet.mem_spec. cbn. firstorder eauto.
Qed.

Lemma clauses_conclusions_clauses_with_concl cls concl :
  LevelSet.Subset (clauses_conclusions (clauses_with_concl cls concl)) concl.
Proof.
  intros x [cl []] % clauses_conclusions_spec.
  eapply in_clauses_with_concl in H as [].
  now rewrite H0 in H.
Qed.

Lemma clauses_conclusions_restrict_clauses cls W :
  LevelSet.Subset (clauses_conclusions (restrict_clauses cls W)) W.
Proof.
  intros x [cl []] % clauses_conclusions_spec.
  eapply in_restrict_clauses in H as [].
  now rewrite H0 in H.
Qed.

Definition in_clauses_conclusions (cls : clauses) (x : Level.t): Prop :=
  exists cl, Clauses.In cl cls /\ (level cl.2) = x.

Definition v_minus_w_bound (W : LevelSet.t) (m : model) :=
  LevelMap.fold (fun w v acc => Nat.max v acc)
    (LevelMapFact.filter (fun l _ => ~~ LevelSet.mem l W) m) 0%nat.

Definition levelexpr_k : LevelExpr.t -> nat := snd.
Coercion levelexpr_k : LevelExpr.t >-> nat.

Definition level_expr_elt : LevelExprSet.elt -> LevelExpr.t := fun x => x.
Coercion level_expr_elt : LevelExprSet.elt >-> LevelExpr.t.

Definition premise_min (l : nonEmptyLevelExprSet) : nat :=
  let (hd, tl) := NonEmptySetFacts.to_nonempty_list l in
  fold_left (B:=LevelExpr.t) (fun min atom => Nat.min atom min) tl hd.

Definition premise_max (l : nonEmptyLevelExprSet) : nat :=
  let (hd, tl) := NonEmptySetFacts.to_nonempty_list l in
  fold_left (B:=LevelExpr.t) (fun min atom => Nat.max atom min) tl hd.

Definition gain (cl : clause) : Z :=
  Z.of_nat (levelexpr_k (concl cl)) - Z.of_nat (premise_min (premise cl)).

Definition max_gain (cls : clauses) :=
  Clauses.fold (fun cl acc => Nat.max (Z.to_nat (gain cl)) acc) cls 0%nat.

Definition max_clause_premise (cls : clauses) :=
  Clauses.fold (fun cl acc => Nat.max (premise_max (premise cl)) acc) cls 0%nat.

Definition model_same_domain (m m' : model) :=
  forall l, LevelMap.In l m <-> LevelMap.In l m'.

#[local] Instance model_same_domain_refl : Reflexive model_same_domain.
Proof. intros m l. reflexivity. Qed.

#[local] Instance model_same_domain_trans : Transitive model_same_domain.
Proof. intros m m' m'' h h' l. rewrite (h l). apply h'. Qed.


Inductive opt_le {A} (le : relation A) : relation (option A) :=
| opt_le_some x y : le x y -> opt_le le (Some x) (Some y)
| opt_le_none_some x : opt_le le None x.
Derive Signature for opt_le.

Instance opt_le_refl {A} (le : relation A) : Reflexive le -> Reflexive (opt_le le).
Proof.
  intros hre x; induction x; constructor; reflexivity.
Qed.

Instance opt_le_trans {A} (le : relation A) : Transitive le -> Transitive (opt_le le).
Proof.
  intros hre x; induction x; destruct y as [y|]; intros z H H'; depelim H; depelim H'; constructor.
  now transitivity y.
Qed.

Infix "≤" := (opt_le Nat.le) (at level 50).

Infix "≤Z" := (opt_le Z.le) (at level 50).

Definition model_rel R (m m' : model) :=
  forall l k, LevelMap.MapsTo l k m -> exists k', LevelMap.MapsTo l k' m' /\ R k k'.

Infix "⩽" := (model_rel Nat.le) (at level 70). (* \leqslant *)

Infix "⩹" := (model_rel Nat.lt) (at level 70).

Definition model_map_outside V (m m' : model) :=
  forall l, ~ LevelSet.In l V ->
    forall k, LevelMap.MapsTo l k m <-> LevelMap.MapsTo l k m'.

#[local] Instance model_map_outside_refl V : Reflexive (model_map_outside V).
Proof. intros m l. reflexivity. Qed.

#[local] Instance model_map_outside_trans V : Transitive (model_map_outside V).
Proof.
  intros m m' m'' h h' l hnin k.
  rewrite (h l hnin k). now apply h'.
Qed.

(** The termination proof relies on the correctness of check_model:
  it does strictly increase a value but not above [max_gain cls].
*)

Lemma clauses_conclusions_diff cls s :
  clauses_conclusions (Clauses.diff cls (clauses_with_concl cls s)) ⊂_lset
  LevelSet.diff (clauses_conclusions cls) s.
Proof.
  intros a. rewrite LevelSet.diff_spec !clauses_conclusions_spec.
  firstorder eauto.
  exists x; split => //.
  now rewrite Clauses.diff_spec in H.
  intros ha.
  rewrite Clauses.diff_spec in H; destruct H as [].
  apply H1.
  rewrite in_clauses_with_concl. split => //.
  now rewrite H0.
Qed.

Lemma diff_eq U V : LevelSet.diff V U =_lset V <-> LevelSet.inter V U =_lset LevelSet.empty.
Proof. split. lsets. lsets. Qed.

Lemma levelset_neq U V : LevelSet.equal U V = false -> ~ LevelSet.Equal U V.
Proof. intros eq heq % LevelSet.equal_spec. congruence. Qed.

Lemma levelset_union_same U : LevelSet.union U U =_lset U.
Proof. lsets. Qed.

Class Commutative {A} (f : A -> A -> A) := comm : forall x y, f x y = f y x.
Instance option_map_2_comm {A} f : @Commutative A f -> @Commutative (option A) (option_map2 f).
Proof.
  intros com [x|] [y|] => //=. now rewrite comm.
Qed.

Instance Zmin_comm : Commutative Z.min := Z.min_comm.
Instance Zmax_comm : Commutative Z.max := Z.max_comm.

Instance nat_min_comm : Commutative Nat.min := Nat.min_comm.
Instance nat_max_comm : Commutative Nat.max := Nat.max_comm.

Class Associative {A} (f : A -> A -> A) := assoc : forall x y z, f x (f y z) = f (f x y) z.
Instance option_map_2_assoc {A} f : @Associative A f -> @Associative (option A) (option_map2 f).
Proof.
  intros assoc [x|] [y|] [z|]; cbn => //. now rewrite assoc.
Qed.

Instance nat_min_assoc : Associative Nat.min := Nat.min_assoc.
Instance nat_max_assoc : Associative Nat.max := Nat.max_assoc.


Instance Zmin_assoc : Associative Z.min := Z.min_assoc.
Instance Zmax_assoc : Associative Z.max := Z.max_assoc.

Lemma fold_left_comm {A B} (f : B -> A -> B) (l : list A) (x : A) (acc : B) :
  (forall x y z, f (f z x) y = f (f z y) x) ->
  fold_left f l (f acc x) = f (fold_left f l acc) x.
Proof.
  intros.
  induction l in acc, x |- *; cbn. auto.
  rewrite -IHl. f_equal. now rewrite H.
Qed.

Lemma fold_left_min_opt_comm {A} (f : A -> A -> A) l x acc :
  Associative f -> Commutative f ->
  fold_left (option_map2 f) l (option_map2 f acc x) = option_map2 f (fold_left (option_map2 f) l acc) x.
Proof.
  intros ass c. rewrite fold_left_comm => //.
  intros. rewrite -(assoc (f := option_map2 f)).
  rewrite -(assoc (f := option_map2 f) z y x0).
  f_equal. apply comm.
Qed.

Lemma fold_left_le {A} {le} (f g : A -> LevelSet.elt -> A) l :
  (forall acc acc'  x, In x l -> le acc acc' -> le (f acc x) (g acc' x)) ->
  forall acc acc', le acc acc' ->
  le (fold_left f l acc) (fold_left g l acc').
Proof.
  intros hfg.
  induction l => //. cbn. intros.
  apply IHl. intros. apply hfg => //. now right. apply hfg => //. now left.
Qed.

Local Open Scope nat_scope.
Lemma fold_left_ne_lt (f g : nat -> LevelSet.elt -> nat) l acc :
  (forall (x y : LevelSet.elt) z, f (f z x) y = f (f z y) x) ->
  (forall (x y : LevelSet.elt) z, g (g z x) y = g (g z y) x) ->
  l <> [] ->
  (forall acc acc' x, In x l -> (acc <= acc') -> (f acc x <= g acc' x)) ->
  (forall acc acc' x, In x l -> (acc < acc') -> (f acc x < g acc' x)) ->
  (exists x, In x l /\ forall acc acc', (acc <= acc') -> (f acc x < g acc' x)) ->
  fold_left f l acc < fold_left g l acc.
Proof.
  intros hf hg.
  generalize (Nat.le_refl acc).
  generalize acc at 2 4.
  induction l in acc |- * => //.
  intros.
  destruct l; cbn.
  { destruct H3 as [x []]. cbn in H3. destruct H3; subst => //.
    now eapply (H4 acc acc0). }
  cbn in IHl.
  rewrite hf hg.
  rewrite fold_left_comm //. rewrite (fold_left_comm g) //.
  destruct H3 as [min [hmin hfg]].
  destruct hmin as [<-|hel].
  - apply hfg. apply fold_left_le => //. intros; eapply H1 => //. now right; right.
    apply H1 => //. now right; left.
  - apply H2. now left. eapply IHl => //.
    * intros acc1 acc' x hin. apply (H1 acc1 acc' x). now right.
    * intros acc1 acc' x hin. apply (H2 acc1 acc' x). now right.
    * exists min. split => //.
Qed.
Close Scope nat_scope.

Infix "↓" := clauses_with_concl (at level 70). (* \downarrow *)
Infix "⇂" := restrict_clauses (at level 70). (* \downharpoonright *)

Lemma clauses_conclusions_diff_left cls W cls' :
  clauses_conclusions (Clauses.diff (cls ↓ W) cls') ⊂_lset W.
Proof.
  intros l.
  rewrite clauses_conclusions_spec.
  move=> [] cl. rewrite Clauses.diff_spec => [] [] [].
  move/in_clauses_with_concl => [] hin ? ? eq.
  now rewrite eq in hin.
Qed.

Lemma clauses_conclusions_diff_restrict cls W cls' :
  clauses_conclusions (Clauses.diff (cls ⇂ W) cls') ⊂_lset W.
Proof.
  intros l.
  rewrite clauses_conclusions_spec.
  move=> [] cl. rewrite Clauses.diff_spec => [] [] [].
  move/in_restrict_clauses => [] hin ? ? ? eq.
  now rewrite eq in hin.
Qed.

Lemma LevelSet_In_elements l s :
  In l (LevelSet.elements s) <-> LevelSet.In l s.
Proof.
  rewrite LevelSetFact.elements_iff.
  now rewrite InA_In_eq.
Qed.

Lemma clauses_empty_eq {s} : Clauses.Empty s -> Clauses.Equal s Clauses.empty.
Proof. clsets. Qed.

Lemma valid_update_value {m cl} :
  valid_clause m cl ->
  match update_value m cl with
  | None => true
  | Some _ => false
  end.
Proof.
  unfold update_value, valid_clause.
  destruct cl as [prem [l k]]; cbn.
  destruct min_premise => //.
  destruct Z.ltb => //.
  unfold level_value_above.
  destruct level_value => //.
  destruct Nat.leb => //.
Qed.

Lemma level_value_not_above_spec m l k : level_value_above m l k = false -> opt_le Nat.lt (level_value m l) (Some k).
Proof.
  unfold level_value_above; destruct level_value => // hlt; constructor. lia.
Qed.

Lemma clauses_for_all_neg {p s}:
  ~~ Clauses.for_all p s <-> ~ Clauses.For_all p s.
Proof.
  intuition auto.
  rewrite ClausesFact.for_all_iff in H0. red in H. now rewrite H0 in H.
  revert H. apply contra_notN.
  rewrite ClausesFact.for_all_iff //.
Qed.

Lemma clauses_for_all_exists {p s}:
  ~~ Clauses.for_all p s <-> Clauses.exists_ (fun x => ~~ p x) s.
Proof.
  rewrite ClausesFact.for_all_b ClausesFact.exists_b.
  induction (Clauses.elements s).
  - cbn; auto. reflexivity.
  - cbn. rewrite negb_and. intuition auto.
    move/orP: H1 => [->|] //. move/H. intros ->. now rewrite orb_true_r.
    move/orP: H1 => [->|] //. move/H0. intros ->. now rewrite orb_true_r.
Qed.
#[local] Instance model_le_refl R (HR : Reflexive R) : Reflexive (model_rel R).
Proof. intros x l k map. exists k; split => //. Qed.

#[local] Instance model_le_trans R (HR : Transitive R) : Transitive (model_rel R).
Proof. intros m m' m'' mm' m'm'' l k map.
  apply mm' in map as [k' [map ?]].
  apply m'm'' in map as [k'' [map ?]]. exists k''. split => //.
  now transitivity k'.
Qed.

Lemma update_model_monotone m l k : level_value m l ≤ Some k -> m ⩽ update_model m l k.
Proof.
  intros hl.
  intros l' k' maps.
  unfold update_model. cbn.
  destruct (eqb_spec l l').
  - subst l'. exists k. move: hl.
    unfold level_value.
    rewrite (LevelMap.find_1 maps).
    intros hle.
    split => //. eapply LevelMap.add_1. eapply LevelMap.OT.eq_refl. now depelim hle.
  - exists k'. split => //. apply LevelMap.add_2 => //.
Qed.

Lemma update_model_not_above m l k : level_value_above m l k = false -> m ⩽ update_model m l k.
Proof.
  unfold level_value_above.
  intros hlev.
  apply update_model_monotone.
  destruct level_value as [v|] eqn:hv; constructor; lia.
Qed.

Lemma level_value_MapsTo {l k} {m : model} :
  LevelMap.MapsTo l k m -> level_value m l = Some k.
Proof.
  unfold level_value.
 move=> mapto; rewrite (LevelMap.find_1 mapto) //.
Qed.

Lemma level_value_MapsTo' {l k} {m : model} :
  level_value m l = Some k -> LevelMap.MapsTo l k m.
Proof.
  unfold level_value. destruct LevelMap.find eqn:hfind => //.
  eapply LevelMap.find_2 in hfind. now intros [= ->].
Qed.

Lemma strict_update_ext m cl m' : strict_update m cl m' -> m ⩽ m'.
Proof.
  destruct cl as [prems [concl k]].
  unfold strict_update.
  intros [v [hm hlt ha heq]].
  intros x k' hin. setoid_rewrite heq.
  setoid_rewrite LevelMapFact.F.add_mapsto_iff.
  destruct (Level.eq_dec concl x). subst.
  move: ha; rewrite /level_value_above.
  eapply level_value_MapsTo in hin. rewrite hin.
  intros hlt'.
  exists (k + Z.to_nat v)%nat.
  split. left. split; reflexivity. red.
  move/negbTE: hlt'.
  elim: Nat.leb_spec => //. lia.
  exists k'. split => //. right; eauto.
Qed.

Lemma strictly_updates_ext cls w m m' : strictly_updates cls w m m' -> m ⩽ m'.
Proof.
  induction 1.
  now eapply strict_update_ext in H0.
  now transitivity m'.
Qed.

Lemma check_model_le {cls acc acc'} :
  check_model cls acc = Some acc' -> acc.2 ⩽ acc'.2.
Proof.
  destruct acc as [w m], acc' as [w' m'].
  move/check_model_spec => [w'' [su ->]].
  cbn. now eapply strictly_updates_ext.
Qed.

Lemma level_value_update_model m l k :
  level_value (update_model m l k) l = Some k.
Proof.
  unfold level_value, update_model.
  cbn -[LevelMap.find LevelMap.add].
  rewrite LevelMapFact.F.add_o.
  destruct LevelMap.OT.eq_dec => //.
  exfalso. now apply n.
Qed.

Lemma model_map_outside_weaken {W W'} {m m' : model} :
  model_map_outside W m m' ->
  W ⊂_lset W' ->
  model_map_outside W' m m'.
Proof.
  intros hm sub x hin k.
  apply hm. intros hin'. apply sub in hin'. now apply hin.
Qed.

Lemma is_model_union {cls cls' m} :
  is_model cls m -> is_model cls' m -> is_model (Clauses.union cls cls') m.
Proof.
  rewrite /is_model. rewrite /is_true -!ClausesFact.for_all_iff.
  now move=> ism ism' x /Clauses.union_spec [].
Qed.

Lemma model_le_values {m m' : model} x : m ⩽ m' -> level_value m x ≤ level_value m' x.
Proof.
  intros lem. specialize (lem x).
  unfold level_value.
  destruct LevelMap.find eqn:hl => //.
  - apply LevelMap.find_2 in hl. specialize (lem _ hl) as [k' [mapsto leq]].
    rewrite (LevelMap.find_1 mapsto). now constructor.
  - constructor.
Qed.

Infix "⊂_clset" := Clauses.Subset (at level 70).

Lemma max_gain_in cl cls :
  Clauses.In cl cls ->
  (Z.to_nat (gain cl) <= max_gain cls)%nat.
Proof.
  intros hin.
  unfold max_gain. revert cl hin.
  eapply ClausesProp.fold_rec.
  - intros s' ise hin. firstorder eauto.
  - intros x a s' s'' xs nxs' hadd IH cl' hin'.
    eapply hadd in hin' as [].
    * subst x. lia.
    * specialize (IH _ H). lia.
Qed.

Definition max_gain_subset (cls cls' : Clauses.t) :
  cls ⊂_clset cls' ->
  (max_gain cls <= max_gain cls')%nat.
Proof.
  unfold max_gain at 1.
  revert cls'.
  eapply ClausesProp.fold_rec.
  - intros s' ise sub. lia.
  - intros x a s' s'' xs nxs' hadd IH cls'' hs.
    specialize (IH cls''). forward IH. transitivity s'' => //.
    intros ??. now apply hadd.
    assert (incls'' : Clauses.In x cls'').
    { now apply hs, hadd. }
    apply max_gain_in in incls''. lia.
Qed.

Lemma max_clause_premise_spec cl cls :
  Clauses.In cl cls ->
  (premise_max (premise cl) <= max_clause_premise cls)%nat.
Proof.
  intros hin.
  unfold max_clause_premise. revert cl hin.
  eapply ClausesProp.fold_rec.
  - intros s' ise hin. firstorder eauto.
  - intros x a s' s'' xs nxs' hadd IH cl' hin'.
    eapply hadd in hin' as [].
    * subst x. lia.
    * specialize (IH _ H). lia.
Qed.

Notation cls_diff cls W := (Clauses.diff (cls ↓ W) (cls ⇂ W)) (only parsing).

(*
  Equations? extend_model {W cls} (m : valid_model W (cls ⇂ W))
    (r : result W (Clauses.diff (cls ↓ W) (cls ⇂ W)))
    : result W (cls ↓ W) :=
    extend_model _ Loop := Loop;
    extend_model m (Model w m' sub) :=
      Model w {| model_model := m'.(model_model) |} _.
  Proof.
    - apply LevelSet.subset_spec in sub. now apply clauses_conclusions_clauses_with_concl in H.
    - eapply sub. now eapply m.(model_clauses_conclusions).
    - apply m.
    - eapply LevelSet.subset_spec. eapply LevelSet.subset_spec in sub.
      now transitivity V.
  Qed.

  *)

Lemma not_mem l s : ~~ LevelSet.mem l s <-> ~ LevelSet.In l s.
Proof.
  split. apply contraNnot. apply LevelSet.mem_spec.
  eapply contra_notN; tea. now move/LevelSet.mem_spec.
Qed.

Lemma v_minus_w_bound_irrel {W} m m' :
  model_map_outside W m m' ->
  v_minus_w_bound W m = v_minus_w_bound W m'.
Proof.
  unfold v_minus_w_bound.
  intros out. eapply LevelMapFact.fold_Equal. tc. cbn.
  { intros x y eq. cbn. solve_proper. }
  { intros x y. cbn. intros e e' a neq. lia. }
  apply LevelMapFact.F.Equal_mapsto_iff.
  intros k e. rewrite -> LevelMapFact.filter_iff.
  2:{ intros x y eq. red in eq. subst; solve_proper. }
  rewrite -> LevelMapFact.filter_iff.
  2:{ move=> x y ->. solve_proper. }
  rewrite [_ = true]not_mem. intuition auto.
  - now apply out.
  - now apply out.
Qed.

Definition max_premise_value (m : model) (l : nonEmptyLevelExprSet) : option nat :=
  let (hd, tl) := NonEmptySetFacts.to_nonempty_list l in
  fold_left (fun min atom => option_map2 Nat.max (levelexpr_value m atom) min) tl (levelexpr_value m hd).

Definition non_W_atoms W (l : LevelExprSet.t) :=
  LevelExprSet.filter (fun lk => ~~ LevelSet.mem lk.1 W) l.

Lemma non_W_atoms_spec W l : forall x, LevelExprSet.In x (non_W_atoms W l) <-> LevelExprSet.In x l /\ ~ LevelSet.In x.1 W.
Proof.
  intros x. now rewrite /non_W_atoms LevelExprSet.filter_spec -not_mem.
Qed.

Lemma non_W_atoms_subset W l : non_W_atoms W l ⊂_leset l.
Proof. intros x. now rewrite /non_W_atoms LevelExprSet.filter_spec. Qed.

Lemma levelexprset_levels_spec_aux l (e : LevelExprSet.t) acc :
  LevelSet.In l (LevelExprSet.fold (fun le : LevelExprSet.elt => LevelSet.add (level le)) e acc) <->
  (exists k, LevelExprSet.In (l, k) e) \/ LevelSet.In l acc.
Proof.
  eapply LevelExprSetProp.fold_rec.
  - intros.
    intuition auto. destruct H1 as [k hin]. lesets.
  - intros x a s' s'' hin nin hadd ih.
    rewrite LevelSet.add_spec.
    split.
    * intros [->|].
      left. exists (levelexpr_k x). red in H. subst.
      apply hadd. cbn. left. now destruct x.
      apply ih in H.
      intuition auto.
      left. destruct H0 as [k Hk]. exists k. apply hadd. now right.
    * intros [[k ins'']|inacc].
      eapply hadd in ins''. destruct ins''; subst.
      + now left.
      + right. apply ih. now left; exists k.
      + right. intuition auto.
Qed.

Lemma levelexprset_levels_spec l (e : LevelExprSet.t) :
  LevelSet.In l (levels e) <-> exists k, LevelExprSet.In (l, k) e.
Proof.
  rewrite levelexprset_levels_spec_aux. intuition auto. lsets.
Qed.

Lemma levels_exprs_non_W_atoms {W prem} :
  LevelSet.Equal (levels (non_W_atoms W prem)) (LevelSet.diff (levels prem) W).
Proof.
  intros e. unfold non_W_atoms.
  rewrite levelexprset_levels_spec LevelSet.diff_spec levelexprset_levels_spec.
  firstorder eauto.
  rewrite LevelExprSet.filter_spec in H. now exists x.
  rewrite LevelExprSet.filter_spec in H. destruct H.
  rewrite LevelSetFact.not_mem_iff.
  destruct LevelSet.mem => //.
  exists x.
  rewrite LevelExprSet.filter_spec. split => //.
  rewrite LevelSetFact.not_mem_iff in H0. now rewrite H0.
Qed.

Lemma levelexprset_empty_levels x : LevelExprSet.Empty x <-> LevelSet.Empty (levels x).
Proof.
  split.
  - intros he.
    intros l hin.
    eapply levelexprset_levels_spec in hin as [k hin]. lesets.
  - intros emp l hin. eapply emp. eapply (levelexprset_levels_spec l.1). exists l.2.
    now destruct l.
Qed.

Lemma non_W_atoms_ne W cl cls :
  Clauses.In cl (cls_diff cls W) ->
  LevelExprSet.is_empty (non_W_atoms W (premise cl)) = false.
Proof.
  intros x.
  apply Clauses.diff_spec in x as [clw clr].
  eapply in_clauses_with_concl in clw as [clw incls].
  apply/negbTE.
  apply/(contra_notN _ clr).
  intros he. rewrite in_restrict_clauses. split => //.
  epose proof (@levels_exprs_non_W_atoms W (premise cl)).
  eapply LevelExprSetFact.is_empty_2 in he.
  intros x hin. eapply levelexprset_empty_levels in he. rewrite H in he.
  specialize (he x). rewrite LevelSet.diff_spec in he. intuition auto.
  rewrite -LevelSet.mem_spec in H1 |- *. destruct LevelSet.mem; intuition auto.
Qed.

Local Open Scope Z_scope.

Section MoreNonEmpty.

  Import LevelExprSet.
  Lemma In_elements {x} {s : LevelExprSet.t} : In x s <-> List.In x (elements s).
  Proof.
    split. now move/LevelExprSetFact.elements_1/InA_In_eq.
    now move/InA_In_eq/LevelExprSetFact.elements_2.
  Qed.
  Import NonEmptySetFacts.

  Notation min_opt := (option_map2 Z.min).
  Lemma Zmin_opt_left x y : min_opt x y ≤Z x.
  Proof.
    destruct x as [x|], y as [y|]; constructor. lia.
  Qed.

  Lemma Zmin_opt_right x y : min_opt x y ≤Z y.
  Proof.
    destruct x as [x|], y as [y|]; constructor. lia.
  Qed.

  Lemma min_opt_spec x y z : min_opt x y = z -> (z = y \/ z = x).
  Proof.
    destruct x as [x|], y as [y|], z as [z|]; cbn; intuition auto.
    - noconf H. pose proof (Zmin_irreducible x y). destruct H; intuition (f_equal; auto).
    - noconf H.
  Qed.

  Lemma min_premise_spec_aux (m : model) s k :
    min_premise m s = k ->
    (forall x, LevelExprSet.In x s -> (k ≤Z min_atom_value m x)) /\
    (exists x, LevelExprSet.In x s /\ k = min_atom_value m x).
  Proof.
    unfold min_premise.
    move: (to_nonempty_list_spec s).
    destruct (to_nonempty_list s). intros heq.
    setoid_rewrite In_elements. rewrite -heq. clear s heq.
    intros <-.
    induction l.
    - cbn.
      split. intros x [->|] => //. reflexivity.
      now exists t0; split => //.
    - destruct IHl as [ha hex].
      split.
      * intros x hin.
        eapply (in_elt_inv x a [t0]) in hin as [<-|inih].
        { cbn. rewrite fold_left_comm.
          { intros x' y z. rewrite assoc. now rewrite (comm (min_atom_value m y)) -assoc. }
          apply Zmin_opt_left. }
      specialize (ha _ inih).
      cbn. rewrite fold_left_comm.
      { intros x' y z. rewrite assoc. now rewrite (comm (min_atom_value m y)) -assoc. }
      etransitivity; [apply Zmin_opt_right|assumption].
      * destruct hex as [minval [inmin ih]].
        cbn. rewrite fold_left_comm.
        { intros x' y z. rewrite assoc. now rewrite (comm (min_atom_value m y)) -assoc. }
        rewrite ih.
        destruct (min_opt_spec (min_atom_value m a) (min_atom_value m minval) _ eq_refl).
        { rewrite H. exists minval. cbn in inmin. split; [intuition|reflexivity]. }
        { rewrite H. exists a. cbn in inmin. split; [intuition|reflexivity]. }
  Qed.

  Lemma min_premise_spec (m : model) (s : nonEmptyLevelExprSet) :
    (forall x, LevelExprSet.In x s -> min_premise m s ≤Z min_atom_value m x) /\
    (exists x, LevelExprSet.In x s /\ min_premise m s = min_atom_value m x).
  Proof.
    now apply min_premise_spec_aux.
  Qed.

  Lemma min_premise_subset (m : model) (s s' : nonEmptyLevelExprSet) :
    LevelExprSet.Subset s s' ->
    min_premise m s' ≤Z min_premise m s.
  Proof.
    intros sub.
    have [has [mins [ins eqs]]] := min_premise_spec m s.
    have [has' [mins' [ins' eqs']]] := min_premise_spec m s'.
    specialize (sub _ ins). specialize (has' _ sub).
    now rewrite eqs.
  Qed.

  Lemma premise_min_spec_aux s k :
    premise_min s = k ->
    (forall x, LevelExprSet.In x s -> (k <= x)%nat) /\
    (exists x, LevelExprSet.In x s /\ k = x).
  Proof.
    unfold premise_min.
    move: (to_nonempty_list_spec s).
    destruct (to_nonempty_list s). intros heq.
    setoid_rewrite In_elements. rewrite -heq. clear s heq.
    intros <-.
    induction l.
    - cbn.
      split. intros x [->|] => //.
      now exists t0; split => //.
    - destruct IHl as [ha hex].
      split; intros.
      eapply (in_elt_inv x a [t0]) in H as [<-|inih].
      cbn. rewrite fold_left_comm. unfold level_expr_elt in *; lia. unfold level_expr_elt in *; lia.
      specialize (ha _ inih).
      cbn. rewrite fold_left_comm. lia. lia.
      destruct hex as [minval [inmin ih]].
      cbn. rewrite fold_left_comm. lia.
      destruct (Nat.leb_spec a minval).
      exists a. split; [intuition|]. rewrite -ih in H. unfold level_expr_elt in *; lia.
      exists minval.
      cbn in inmin; split; [intuition auto|]. lia.
  Qed.

  Lemma premise_min_spec (s : nonEmptyLevelExprSet) :
    (forall x, LevelExprSet.In x s -> premise_min s <= x)%nat /\
    (exists x, LevelExprSet.In x s /\ premise_min s = x).
  Proof.
    now apply premise_min_spec_aux.
  Qed.

  Lemma premise_max_spec_aux s k :
    premise_max s = k ->
    (forall x, LevelExprSet.In x s -> (x <= k)%nat) /\
    (exists x, LevelExprSet.In x s /\ k = x).
  Proof.
    unfold premise_max.
    move: (to_nonempty_list_spec s).
    destruct (to_nonempty_list s). intros heq.
    setoid_rewrite In_elements. rewrite -heq. clear s heq.
    intros <-.
    induction l.
    - cbn.
      split. intros x [->|] => //.
      now exists t0; split => //.
    - destruct IHl as [ha hex].
      split; intros.
      eapply (in_elt_inv x a [t0]) in H as [<-|inih].
      cbn. rewrite fold_left_comm. unfold level_expr_elt in *; lia. unfold level_expr_elt in *; lia.
      specialize (ha _ inih).
      cbn. rewrite fold_left_comm. lia. lia.
      destruct hex as [maxval [inmin ih]].
      cbn. rewrite fold_left_comm. lia.
      destruct (Nat.leb_spec a maxval).
      exists maxval. cbn in inmin; split; [intuition auto|]. lia.
      exists a. split; [intuition|]. rewrite -ih in H. cbn in inmin.
      unfold level_expr_elt in *; lia.
  Qed.

  Lemma premise_max_spec (s : nonEmptyLevelExprSet) :
    (forall x, LevelExprSet.In x s -> x <= premise_max s)%nat /\
    (exists x, LevelExprSet.In x s /\ premise_max s = x).
  Proof.
    now apply premise_max_spec_aux.
  Qed.

  Lemma premise_min_subset (s s' : nonEmptyLevelExprSet) :
    LevelExprSet.Subset s s' ->
    (premise_min s' <= premise_min s)%nat.
  Proof.
    intros sub.
    have [has [mins [ins eqs]]] := premise_min_spec s.
    have [has' [mins' [ins' eqs']]] := premise_min_spec s'.
    specialize (sub _ ins). specialize (has' _ sub).
    lia.
  Qed.

  Lemma fold_comm_assoc_nat x y z : option_map2 Nat.max x (option_map2 Nat.max y z) =
    option_map2 Nat.max y (option_map2 Nat.max x z).
  Proof.
    now rewrite (assoc (f := option_map2 Nat.max)) (comm (f := option_map2 Nat.max) x y) -assoc.
  Qed.

  Lemma fold_comm_assoc x y z : option_map2 Z.max x (option_map2 Z.max y z) =
    option_map2 Z.max y (option_map2 Z.max x z).
  Proof.
    now rewrite (assoc (f := option_map2 Z.max)) (comm (f := option_map2 Z.max) x y) -assoc.
  Qed.

  Notation max_opt := (option_map2 Nat.max).

  Lemma max_opt_spec x y z : max_opt x y = Some z -> exists x' y', x = Some x' /\ y = Some y' /\ z = Nat.max x' y'.
  Proof.
    destruct x as [x|], y as [y|]; cbn; intuition eauto; try noconf H.
    exists x, y. auto.
  Qed.

  Lemma max_premise_value_spec_aux (m : model) s k :
    max_premise_value m s = Some k ->
    (forall x, LevelExprSet.In x s -> exists k', levelexpr_value m x = Some k' /\ Some k' ≤ Some k) /\
    (exists x, LevelExprSet.In x s /\ Some k = levelexpr_value m x).
  Proof.
    unfold max_premise_value.
    move: (to_nonempty_list_spec s).
    destruct (to_nonempty_list s). intros heq.
    setoid_rewrite In_elements. rewrite -heq. clear s heq.
    induction l in k |- *.
    - cbn.
      intros eq.
      split. intros x [->|] => //. exists k. split => //. reflexivity.
      now exists t0; split => //.
    - cbn. rewrite fold_left_comm. intros; apply fold_comm_assoc_nat.
      intros heq. apply max_opt_spec in heq as [y' [z' [eqa [eqf ->]]]].
      specialize (IHl _ eqf). destruct IHl as [ha hex].
      split; intros.
      eapply (in_elt_inv x a [t0]) in H as [<-|inih].
      { exists y'; intuition eauto. constructor; lia. }
      { specialize (ha _ inih) as [k' []]. exists k'; intuition eauto. constructor. depelim H0; lia. }
      destruct hex as [maxval [inmax ih]].
      cbn.
      destruct (Nat.leb_spec z' y').
      exists a. split; [intuition|]. rewrite eqa. f_equal. lia.
      exists maxval. cbn in inmax; split; [intuition auto|]. rewrite -ih. f_equal; lia.
  Qed.

  Lemma max_premise_value_spec (m : model) (s : nonEmptyLevelExprSet) k :
    max_premise_value m s = Some k ->
    (forall x, LevelExprSet.In x s -> exists k', levelexpr_value m x = Some k' /\ Some k' ≤ Some k) /\
    (exists x, LevelExprSet.In x s /\ Some k = levelexpr_value m x).
  Proof.
    apply (max_premise_value_spec_aux m s).
  Qed.
End MoreNonEmpty.

Lemma min_premise_pos_spec {m prem k} :
  min_premise m prem = Some k ->
  forall x, LevelExprSet.In x prem -> Some (Z.of_nat (levelexpr_k x) + k)%Z ≤Z option_map Z.of_nat (levelexpr_value m x).
Proof.
  pose proof (min_premise_spec m prem) as [amin [exmin [inminpre eqminpre]]].
  intros hprem x hin.
  specialize (amin _ hin).
  unfold min_atom_value in amin.
  destruct x as [l k']; cbn in *. unfold levelexpr_value; cbn.
  destruct (level_value m l) eqn:he.
  - depelim amin.
    rewrite H0 in hprem. depelim hprem. constructor. lia.
    constructor.
    rewrite H in hprem; depelim hprem.
  - depelim amin. rewrite H in hprem. depelim hprem.
Qed.

Lemma min_premise_pos_spec_inv {m} {prem: nonEmptyLevelExprSet} :
  (forall x, LevelExprSet.In x prem -> exists k, levelexpr_value m x = Some k) ->
  exists k, min_premise m prem = Some k.
Proof.
  intros hprem.
Admitted.

Lemma v_minus_w_bound_spec W m :
  forall x, ~ LevelSet.In x W -> level_value m x ≤ Some (v_minus_w_bound W m).
Proof.
  intros x him.
  unfold v_minus_w_bound.
  set (fm := LevelMapFact.filter _ _).
  replace (level_value m x) with (level_value fm x).
  2:{ unfold level_value.
      destruct LevelMap.find eqn:hl => //.
      eapply LevelMap.find_2 in hl.
      subst fm. cbn in hl.
      eapply LevelMapFact.filter_iff in hl as []. 2:tc.
      rewrite (LevelMap.find_1 H) //.
      destruct (LevelMap.find _ m) eqn:hl' => //.
      eapply LevelMap.find_2 in hl'.
      assert (LevelMap.MapsTo x n fm).
      eapply LevelMapFact.filter_iff. tc.
      split => //. now rewrite [_ = true]not_mem.
      now rewrite (LevelMap.find_1 H)  in hl. }
  clearbody fm.
  eapply LevelMapFact.fold_rec.
  - intros m' em. unfold level_value.
    destruct LevelMap.find eqn:hl => //.
    eapply LevelMap.find_2 in hl.
    now apply em in hl. constructor.
  - intros k e a m' m'' map nin hadd.
    red in hadd.
    unfold level_value. cbn.
    rewrite hadd LevelMapFact.F.add_o.
    destruct LevelMap.OT.eq_dec. do 2 red in e0. subst x.
    intros hf. constructor. lia.
    destruct LevelMap.find => hf; depelim hf; constructor; lia.
Qed.

Lemma clauses_levels_restrict_clauses cls W :
  clauses_levels (cls ⇂ W) ⊂_lset W.
Proof.
  intros x [cl []] % clauses_levels_spec.
  eapply in_restrict_clauses in H as [hconc hprem incl].
  eapply clause_levels_spec in H0 as []. apply hprem, H. now subst x.
Qed.

Lemma clauses_conclusions_levels cls :
  clauses_conclusions cls ⊂_lset clauses_levels cls.
Proof.
  intros x.
  rewrite clauses_conclusions_spec clauses_levels_spec.
  setoid_rewrite clause_levels_spec.
  firstorder auto.
Qed.

Record model_extension W m m' :=
  { model_ext_le : m ⩽ m';
    model_ext_same_domain : model_same_domain m m';
    model_ext_same_outside : model_map_outside W m m' }.

#[local] Instance model_ext_reflexive W : Reflexive (model_extension W).
Proof.
  intros m; split; reflexivity.
Qed.

#[local] Instance model_ext_transitive W : Transitive (model_extension W).
Proof.
  intros m m' m'' h h'; split; (etransitivity; [apply h|apply h']).
Qed.

Lemma model_extension_weaken W W' m m' :
  W ⊂_lset W' ->
  model_extension W m m' ->
  model_extension W' m m'.
Proof.
  intros leW []; split => //.
  eapply model_map_outside_weaken; tea.
Qed.

Lemma model_ext_trans_weaken W W' m m' m'' :
  W ⊂_lset W' ->
  model_extension W m m' ->
  model_extension W' m' m'' ->
  model_extension W' m m''.
Proof.
  intros leW mext mext'. eapply model_extension_weaken in mext; tea.
  now etransitivity; tea.
Qed.

Definition model_of V (m : model) :=
  forall k, LevelSet.In k V -> LevelMap.In k m.

Definition only_model_of V (m : model) :=
  forall k, LevelSet.In k V <-> exists x, LevelMap.MapsTo k x m.

Definition check_model_invariants cls w m w' m' (modified : bool) :=
  if modified then
    [/\ w ⊂_lset w',
        w' ⊂_lset (LevelSet.union w (clauses_conclusions cls)),
        exists cl,
          let cll := (levelexpr_level (concl cl)) in
          [/\ Clauses.In cl cls, ~~ valid_clause m cl,
          LevelSet.In cll w' &
          opt_le Nat.lt (level_value m cll) (level_value m' cll)],
          model_extension w' m m' &
          model_of w' m']
  else (w, m) = (w', m') /\ model_of w m.

Lemma nEmpty_exists ls : ~ (LevelSet.Empty ls) -> exists l, LevelSet.In l ls.
Proof.
  intros ne.
  destruct (LevelSet.choose ls) eqn:isempty. exists e.
  now apply LevelSet.choose_spec1 in isempty.
  now apply LevelSet.choose_spec2 in isempty.
Qed.

Lemma inLevelSet (ls : LevelSet.t) l : LevelSet.In l ls \/ ~ (LevelSet.In l ls).
Proof.
  lsets.
Qed.

Lemma level_value_above_MapsTo m l k : level_value_above m l k -> exists k', LevelMap.MapsTo l k' m /\ (k <= k')%nat.
Proof.
  unfold level_value_above.
  destruct level_value eqn:hl => //.
  move/Nat.leb_le => hle; exists n.
  eapply level_value_MapsTo' in hl. split => //.
Qed.

Lemma level_value_above_MapsTo' m l k k' : LevelMap.MapsTo l k' m -> (k <= k')%nat -> level_value_above m l k.
Proof.
  unfold level_value_above.
  intros H; apply LevelMap.find_1 in H. rewrite /level_value H.
  intros hleq; depelim hleq; now apply Nat.leb_le.
Qed.

Lemma level_value_add m l k : level_value (LevelMap.add l k m) l = Some k.
Proof.
  rewrite /level_value LevelMapFact.F.add_eq_o //.
Qed.

#[local] Instance clauses_conclusions_proper : Proper (Clauses.Equal ==> LevelSet.Equal) clauses_conclusions.
Proof.
  intros cls cls' eq x.
  rewrite !clauses_conclusions_spec. now setoid_rewrite eq.
Qed.

#[local] Instance And3P_proper : Proper (iff ==> iff ==> iff ==> iff) ssrbool.and3.
Proof.
  repeat intro. split; intros []; split; intuition auto.
Qed.

#[local] Instance And4P_proper : Proper (iff ==> iff ==> iff ==> iff ==> iff) ssrbool.and4.
Proof.
  repeat intro. split; intros []; split; intuition auto.
Qed.

#[local] Instance And5P_proper : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff) ssrbool.and5.
Proof.
  repeat intro. split; intros []; split; intuition auto.
Qed.

#[local] Instance check_model_invariants_proper :
  Proper (Clauses.Equal ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) check_model_invariants.
Proof.
  intros cls cls' eqcls.
  repeat intro; subst.
  unfold check_model_invariants.
  destruct y3 => //.
  now setoid_rewrite <-eqcls.
Qed.

Lemma min_atom_value_levelexpr_value m l a lv : min_atom_value m l = Some a -> levelexpr_value m l = Some lv ->
  (a <= (Z.of_nat lv - Z.of_nat l))%Z.
Proof.
  destruct l as [l k]; cbn. unfold levelexpr_value. cbn. destruct level_value => //.
  intros [= <-] [= <-]. lia.
Qed.

Lemma clauses_conclusions_add cl cls :
  clauses_conclusions (Clauses.add cl cls) =_lset
  (LevelSet.singleton (level (concl cl)) ∪
    clauses_conclusions cls).
Proof.
  intros x.
  rewrite LevelSet.union_spec !clauses_conclusions_spec.
  setoid_rewrite Clauses.add_spec; setoid_rewrite LevelSet.singleton_spec.
  firstorder eauto. subst. now left.
Qed.

Definition declared_model_level (m : model) l := LevelMap.In l m.

Definition update_model_same_domain {m l k} :
  declared_model_level m l ->
  model_same_domain m (update_model m l k).
Proof.
  unfold update_model, declared_model_level.
  intros hin x.
  rewrite LevelMapFact.F.add_in_iff. intuition auto. now subst.
Qed.

Definition update_model_outside {m w l k} :
  model_map_outside (LevelSet.add l w) m (update_model m l k).
Proof.
  unfold update_model, model_map_outside.
  intros l'. rewrite LevelSet.add_spec.
  intros hin k'.
  rewrite LevelMapFact.F.add_neq_mapsto_iff //.
  intros heq. red in heq; subst l'. apply hin. now left.
Qed.

Lemma opt_lt_le_trans x y z :
  opt_le Z.lt x y ->
  opt_le Z.le y z ->
  opt_le Z.lt x z.
Proof.
  intros [] H'; depelim H'; constructor. lia.
Qed.

Lemma model_of_update w m l k : model_of w m -> model_of (LevelSet.add l w) (update_model m l k).
Proof.
  rewrite /model_of => hint l'. rewrite LevelSet.add_spec.
  intros [->|hadd].
  - exists k. now apply LevelMap.add_1.
  - specialize (hint _ hadd). unfold update_model.
    destruct hint as [x hx].
    destruct (eqb_spec l l'). subst.
    now exists k; apply LevelMap.add_1.
    now exists x; eapply LevelMap.add_2.
Qed.

Definition levelset_m_eq : list Level.t × model -> list Level.t × model -> Prop :=
  fun x y => x.1 = y.1 /\ LevelMap.Equal x.2 y.2.

#[local] Instance lmeq_eq : Equivalence levelset_m_eq.
Proof.
  split. intros x. split => //.
  intros x y []; split => //.
  intros x y z [] []; split => //.
  all:etransitivity; tea.
Qed.

(* Definition optm := optm *)

(* #[local] Instance update_value_proper : Proper (LevelMap.Equal ==> eq ==> opt ) update_value. *)

#[local] Instance check_clause_model_proper : Proper (eq ==> levelset_m_eq ==> levelset_m_eq) check_clause_model.
Proof.
  intros x y eq [] [] []; cbn in *; subst.
  unfold levelset_m_eq.
  replace (update_value m y) with (update_value m0 y). split => //; destruct update_value => //.
  unfold update_value. setoid_rewrite H0.
Abort.

Instance model_map_outside_proper : Proper (LevelSet.Equal ==> LevelMap.Equal ==> LevelMap.Equal ==> iff) model_map_outside.
Proof.
  intros ? ? eqcl ? ? eqm ? ? eqs.
  unfold model_map_outside.
  setoid_rewrite eqcl. now setoid_rewrite eqm; setoid_rewrite eqs.
Qed.

#[local] Instance proper_levelexprset_levels : Proper (LevelExprSet.Equal ==> LevelSet.Equal)
  levels.
Proof.
  intros s s' eq l.
  rewrite !levelexprset_levels_spec.
  firstorder eauto.
Qed.

(* Lemma min_premise_some_pres {m m' prems k} : m ⩽ m' -> min_premise m prems = Some k -> exists k', min_premise m' prems = Some k'.
Proof.
  intros ext minp.
  apply (@min_premise_pos_spec_inv m' prems).
  intros x hin.
  pose proof (min_premise_spec m prems) as [le eq]. specialize (le x hin).
  rewrite minp in le. depelim le.
  move: H0; rewrite /min_atom_value /levelexpr_value /level_value. destruct x as [l k'].
  destruct LevelMap.find eqn:hfind => //. intros [= <-].
  eapply LevelMap.find_2 in hfind. eapply ext in hfind as [? [map2 hsome]].
  eapply LevelMap.find_1 in map2. rewrite map2. depelim hsome. now exists n.
Qed. *)

Lemma min_premise_spec' {m prems z} : min_premise m prems = Some z ->
  (forall l k, LevelExprSet.In (l, k) prems ->
  exists v, level_value m l = Some v /\ z <= (Z.of_nat v - Z.of_nat k))%Z.
Proof.
  intros hmin.
  have [hall hhmin'] := min_premise_spec m prems.
  intros l k hin; specialize (hall _ hin). rewrite hmin in hall.
  depelim hall. destruct level_value => //. noconf H0. exists n. split => //.
Qed.

Lemma nonEmptyLevelExprSet_elim {P : nonEmptyLevelExprSet -> Prop} :
  (forall le, P (singleton le)) ->
  (forall le prems, P prems -> P (add le prems)) ->
  forall prems, P prems.
Proof.
  intros hs ha.
  intros [].
  revert t_set0 t_ne0.
  apply: LevelExprSetProp.set_induction; eauto.
  - move=> s /LevelExprSetFact.is_empty_1 he ne; exfalso => //. congruence.
  - intros s s' IH x nin hadd hne.
    destruct (LevelExprSet.is_empty s) eqn:hem in |- .
    eapply LevelExprSetFact.is_empty_2 in hem.
      assert (singleton x = {| t_set := s'; t_ne := hne |}) as <- => //.
      unfold singleton. apply eq_univ'. cbn.
      intros a. specialize (hadd a). rewrite hadd.
      rewrite LevelExprSet.singleton_spec. firstorder. subst. reflexivity.
      specialize (IH hem).
      specialize (ha x _ IH).
      assert (LevelExprSet.Equal (add x {| t_set := s; t_ne := hem|}) {| t_set := s'; t_ne := hne |}).
      2:{ apply eq_univ' in H. now rewrite -H. }
      intros x'. specialize (hadd x'). rewrite LevelExprSet.add_spec.
      cbn. firstorder. subst x'. now left.
Qed.

Lemma min_premise_pres {m m'} prems : m ⩽ m' -> min_premise m prems ≤Z min_premise m' prems.
Proof.
  intros ext.
  destruct (min_premise m prems) eqn:hmin.
  have leq := min_premise_spec' hmin. 2:constructor.
  have [leq' e'] := min_premise_spec m' prems.
  destruct (min_premise_spec m prems) as [_ [minz [inminz eqminz]]].
  rewrite hmin in eqminz.
  rewrite eqminz. destruct e' as [min' []]. rewrite H0.
  transitivity (min_atom_value m min').
  2:{ unfold min_atom_value. destruct min'.
    unfold level_value. destruct (LevelMap.find t m) eqn:hfind. 2:constructor.
    apply LevelMap.find_2 in hfind. apply ext in hfind as [k' [hfind hle]].
    apply LevelMap.find_1 in hfind. rewrite hfind. depelim hle. constructor. lia. constructor. lia.
    }
  destruct min'. specialize (leq _ _ H) as [? []].
  unfold min_atom_value at 2. rewrite H1. rewrite -eqminz. constructor. lia.
Qed.

Lemma level_value_above_mon m m' l k : m ⩽ m' -> level_value_above m l k -> level_value_above m' l k.
Proof.
  intros ext; move/level_value_above_MapsTo => [v [hm hleq]].
  eapply ext in hm. destruct hm as [v' [hm' leq']].
  eapply level_value_above_MapsTo'; tea. lia.
Qed.

Lemma model_of_subset V V' m :
  model_of V m -> V' ⊂_lset V -> model_of V' m.
Proof.
  intros ih hv k. specialize (ih k).
  now move/hv.
Qed.

Instance only_model_of_proper : Proper (LevelSet.Equal ==> LevelMap.Equal ==> iff) only_model_of.
Proof.
  intros ? ? eq ? ? eq'.
  rewrite /only_model_of. now setoid_rewrite eq; setoid_rewrite eq'.
Qed.

Lemma only_model_of_eq V V' m :
  only_model_of V m -> V' =_lset V -> only_model_of V' m.
Proof.
  intros ih hv k. now rewrite hv.
Qed.

Lemma model_of_sub V m : model_of V m -> model_of V m.
Proof.
  rewrite /model_of /model_of.
  intros H k hin. specialize (H k hin) as [? ?].
  now exists x.
Qed.
Coercion model_of_sub : model_of >-> model_of.

Lemma clauses_conclusions_subset {cls cls'} :
  Clauses.Subset cls cls' ->
  clauses_conclusions cls ⊂_lset clauses_conclusions cls'.
Proof.
  intros hsub x. rewrite !clauses_conclusions_spec.
  intuition eauto. destruct H as [cl []]; exists cl; split; try clsets; auto.
Qed.

Lemma check_model_ext {cls w init_model m w' m'} :
  check_model cls (w, m) = Some (w', m') ->
  strictly_updates cls w init_model m ->
  strictly_updates cls w' init_model m' /\ w ⊂_lset w'.
Proof.
  move/check_model_updates_spec.
  intros ih cls'. eapply ih in cls' as [su incl]. split => //.
  eapply strictly_updates_weaken; tea. clsets.
Qed.

Lemma check_model_updates_spec_empty {cls m w m'} :
  check_model cls (LevelSet.empty, m) = Some (w, m') ->
  strictly_updates cls w m m'.
Proof.
  move/check_model_spec => [w' [su ->]].
  replace (LevelSet.union LevelSet.empty w') with w' => //.
  eapply LevelSet.eq_leibniz. intros x; lsets.
Qed.

Lemma check_model_is_model {W cls m} :
  check_model cls (W, m) = None <-> is_model cls m.
Proof.
  now rewrite check_model_None.
Qed.

Lemma check_model_update {W cls m wm'} :
  model_of (clauses_conclusions cls) m ->
  model_of W m ->
  check_model cls (W, m) = Some wm' -> ~~ is_model cls m /\ m ⩽ wm'.2.
Proof.
  intros mof tot.
  destruct wm'.
  move/check_model_spec => [w'' [su ->]]. cbn. split.
  now eapply strictly_updates_invalid.
  now eapply strictly_updates_ext.
Qed.

Definition level_value_default m l :=
  match level_value m l with Some x => x | None => 0 end%nat.

Definition measure_w W cls m w :=
  let bound := v_minus_w_bound W m in
  let maxgain := max_gain (cls_diff cls W) in
  (Z.of_nat bound + Z.of_nat maxgain - Z.of_nat (level_value_default m w))%Z.

Lemma min_premise_max_premise m prem k :
  min_premise m prem = Some k ->
  exists k', max_premise_value m prem = Some k'.
Proof.
  unfold min_premise, max_premise_value.
  destruct to_nonempty_list.
  assert (forall l k, fold_left
  (fun (min : option Z) (atom : LevelExpr.t) =>
   option_map2 Z.min (let '(l0, k0) := atom in match level_value m l0 with
                                               | Some val => Some (Z.of_nat val - Z.of_nat k0)%Z
                                               | None => None
                                               end) min)
  l None =
    Some k -> False).
  { clear. induction l; cbn => //. cbn in *.
    destruct a, level_value; cbn; auto. }
  assert
    (forall x y, fold_left (fun (min : option Z) (atom : LevelExpr.t) => option_map2 Z.min (min_atom_value m atom) min) l (Some x) = Some k ->
exists k',
  fold_left (fun (min : option nat) (atom : LevelExpr.t) => option_map2 Nat.max (levelexpr_value m atom) min) l (Some y) = Some k').
  { induction l; cbn.
    - intros x y [= <-]. now eexists.
    - intros x y.
      unfold min_atom_value, levelexpr_value, levelexpr_level. destruct a; cbn.
      destruct level_value => //=. eapply IHl. cbn. intros H'. exfalso.
      eapply H; eauto. }
  - unfold min_atom_value, levelexpr_value, levelexpr_level. destruct t; cbn.
    destruct level_value => //=. apply H0.
    intros; exfalso. now eapply H.
Qed.

Lemma model_of_value_None W m l :
  model_of W m ->
  LevelSet.In l W ->
  level_value m l = None -> False.
Proof.
  intros tm inw. specialize (tm l inw) as [v hm].
  rewrite /level_value.
  now rewrite (LevelMap.find_1 hm).
Qed.

Lemma invalid_clause_measure W cls cl m :
  model_of W m ->
  ~~ valid_clause m cl ->
  Clauses.In cl (cls_diff cls W) ->
  (0 < measure_w W cls m (concl cl))%Z.
Proof.
  intros hwv. unfold valid_clause.
  (* case: Z.ltb_spec => // hprem. *)
  destruct cl as [prem [l k]]; cbn.
  destruct min_premise eqn:hmin => //.
  elim: Z.ltb_spec => // hle.
  move/negbTE/level_value_not_above_spec => hlt hin.
  have hne := (non_W_atoms_ne _ _ _ hin).
  cbn. unfold measure_w. unfold gain.
  set (clsdiff := Clauses.diff _ _).
  set (bound := v_minus_w_bound W m).
  enough (Z.of_nat (level_value_default m l) < Z.of_nat bound + Z.of_nat (max_gain clsdiff))%Z. lia.
  set (prem' := non_W_atoms W prem).
  set (preml := {| t_set := prem'; t_ne := hne |}).
  assert (Z.to_nat (gain (preml, (l, k))) <= max_gain clsdiff)%nat.
  { transitivity (Z.to_nat (gain (prem, (l, k)))). 2:now apply max_gain_in.
    unfold gain. cbn.
    pose proof (premise_min_subset preml prem).
    rewrite !Z2Nat.inj_sub //; try lia. rewrite !Nat2Z.id.
    forward H. eapply non_W_atoms_subset. lia. }
  eapply Z.lt_le_trans with (Z.of_nat bound + Z.of_nat (Z.to_nat (gain (preml, (l, k)))))%Z; try lia.
  unfold gain; cbn.
  enough (Z.of_nat (level_value_default m l) < Z.of_nat (v_minus_w_bound W m) + Z.of_nat (k - premise_min preml))%Z. lia.
  unfold level_value_default. destruct (level_value m l) as [vl|] eqn:hl; revgoals.
  { eapply model_of_value_None in hl; tea => //.
    eapply Clauses.diff_spec in hin as [hin _].
    now apply in_clauses_with_concl in hin as [hin _]. }
  depelim hlt.
  enough (Z.of_nat k + z <= Z.of_nat (v_minus_w_bound W m) + Z.of_nat (k - premise_min preml))%Z. lia.
  assert (min_premise m prem ≤Z min_premise m preml)%Z.
  { eapply min_premise_subset. eapply non_W_atoms_subset. }
  rewrite hmin in H1. depelim H1.
  transitivity (Z.of_nat k + y)%Z. lia.
  pose proof (min_premise_spec m preml) as [amin [exmin [inminpre eqminpre]]].
  have [maxpreml eqmax] := min_premise_max_premise m preml _ H2.
  pose proof (max_premise_value_spec m preml _ eqmax) as [amax [exmax [inmaxpre eqmaxpre]]].
  pose proof (premise_min_spec preml) as [apmin [expmin [inpminpre eqpminpre]]].
  assert (premise_min prem <= premise_min preml)%nat.
  { eapply premise_min_subset. eapply non_W_atoms_subset. }
  (* transitivity (v_minus_w_bound W m + (k - premise_min preml)). 2:lia. *)
  assert (y <= Z.of_nat maxpreml - Z.of_nat (premise_min preml))%Z.
  { rewrite eqpminpre. rewrite H2 in eqminpre; symmetry in eqminpre.
   (* eqmaxpre eqminpre. *)
    pose proof (min_atom_value_levelexpr_value m exmin).
    specialize (amax _ inminpre) as amax'. rewrite eqmaxpre in amax'.
    destruct amax' as [vexmin [eqexmin ltexmin]].
    assert (expmin <= exmin)%nat. specialize (apmin _ inminpre). lia.
    specialize (H4 _ _ eqminpre eqexmin). depelim ltexmin. etransitivity; tea.
    rewrite -eqmaxpre in H6. noconf H6.
    unfold level_expr_elt in *. lia. }
  transitivity (Z.of_nat k + (Z.of_nat maxpreml - Z.of_nat (premise_min preml)))%Z. lia.
  (* assert (Z.of_nat (premise_min preml) <= maxpreml)%Z.
  { rewrite eqmaxpre.
    move/min_premise_pos_spec: hprem => hprem.
    transitivity exmax. apply apmin => //. eapply hprem.
    now apply (non_W_atoms_subset W prem). } *)
  assert (Z.of_nat k + (Z.of_nat maxpreml - Z.of_nat (premise_min preml)) =
    (Z.of_nat maxpreml + Z.of_nat k - Z.of_nat (premise_min preml)))%Z as ->. lia.
  enough (Z.of_nat maxpreml <= Z.of_nat (v_minus_w_bound W m))%Z. lia.
  { have vm := v_minus_w_bound_spec W m exmax. unfold levelexpr_value in eqmaxpre.
    rewrite -eqmaxpre in vm.
    have [hlevels _] := (@levels_exprs_non_W_atoms W prem (levelexpr_level exmax)).
    rewrite levelexprset_levels_spec in hlevels.
    forward hlevels.
    exists exmax.2. now destruct exmax.
    rewrite LevelSet.diff_spec in hlevels.
    destruct hlevels as [_ nw]. specialize (vm nw). depelim vm. lia. }
Qed.

Module ClausesOrd := OrdProperties Clauses.


#[local] Instance check_model_aux_proper_eq : Proper (Clauses.Equal ==> eq ==> eq) check_model_aux.
Proof.
  intros cls cls' eq.
  intros wm wm' eq'. subst wm'.
  unfold check_model_aux.
  now eapply ClausesOrd.fold_equal; tc.
Qed.

(* #[local] Instance check_model_aux_proper : Proper (Clauses.Equal ==> levelset_m_eq ==> modified_levelset_m_eq) check_model_aux.
Proof.
  intros cls cls' eq.
  intros wm wm' eq'.
  transitivity (check_model_aux cls' wm).
  2:{ unfold check_model_aux.
      eapply (ClausesProp.fold_init (eqA := modified_levelset_m_eq)); tc.
      red. cbn => //. }
  unfold check_model_aux.
  now eapply ClausesOrd.fold_equal; tc.
Qed. *)

(*
#[local] Instance check_model_proper_eq : Proper (Clauses.Equal ==> eq ==> eq) check_model.
Proof.
  intros cls cls' eq.
  intros wm wm' eq'.
  unfold check_model.
  now subst wm'; rewrite eq.
Qed. *)

Definition is_update_of cls upd minit m :=
  if LevelSet.is_empty upd then minit =m m
  else strictly_updates cls upd minit m.

Record valid_model_def (V W : LevelSet.t) (m : model) (cls : clauses) :=
  { model_model : model;
    model_of_V :> model_of V model_model;
    model_updates : is_update_of cls W m model_model;
    model_clauses_conclusions : clauses_conclusions cls ⊂_lset V;
    model_ok :> is_model cls model_model;
 }.
Arguments model_model {V W m cls}.
Arguments model_of_V {V W m cls}.
Arguments model_updates {V W m cls}.
Arguments model_clauses_conclusions {V W m cls}.
Arguments model_ok {V W m cls}.
Extraction Inline model_model.

Definition valid_model := valid_model_def.

Definition add_expr n '((l, k) : LevelExpr.t) := (l, k + n)%nat.

Lemma add_expr_add_expr n n' lk : add_expr n (add_expr n' lk) = add_expr (n + n') lk.
Proof. destruct lk; unfold add_expr. f_equal; lia. Qed.
Definition add_prems n s := map (add_expr n) s.

Lemma In_add_prems k (prems : nonEmptyLevelExprSet):
  forall le, LevelExprSet.In le (add_prems k prems) <->
    exists le', LevelExprSet.In le' prems /\ le = add_expr k le'.
Proof.
  intros [l k'].
  now rewrite /add_prems map_spec.
Qed.


Lemma map_map f g x : map f (map g x) = map (f ∘ g) x.
Proof.
  apply eq_univ'.
  intros lk.
  rewrite !map_spec. setoid_rewrite map_spec.
  firstorder eauto. subst. firstorder.
Qed.

Lemma add_prems_add_prems n n' lk : add_prems n (add_prems n' lk) = add_prems (n + n') lk.
Proof. destruct lk; unfold add_prems.
  rewrite map_map. apply eq_univ'.
  intros x; rewrite /= !map_spec. cbn in *.
  firstorder eauto. subst. exists x0.
  firstorder eauto. now rewrite add_expr_add_expr.
  subst. exists x0.
  firstorder eauto. now rewrite add_expr_add_expr.
Qed.

Definition add_clause n '((prems, concl) : clause) := (add_prems n prems, add_expr n concl).

Lemma add_clause_add_clause n n' cl : add_clause n (add_clause n' cl) = add_clause (n + n') cl.
Proof.
  destruct cl.
  unfold add_clause.
  now rewrite add_prems_add_prems add_expr_add_expr.
Qed.

Notation succ_expr := (add_expr 1).
Notation succ_prems := (add_prems 1).
Notation succ_clause := (add_clause 1).

Lemma succ_clause_inj x y : succ_clause x = succ_clause y -> x = y.
Proof. Admitted.
Definition add_clauses n cls := ClausesProp.of_list (List.map (fun cl => add_clause n cl) (ClausesProp.to_list cls)).
Notation succ_clauses := (add_clauses 1).
Import SetoidList.
Lemma succ_clauses_spec cl cls : Clauses.In cl cls <-> Clauses.In (succ_clause cl) (succ_clauses cls).
Proof.
  unfold succ_clauses.
  rewrite ClausesProp.of_list_1 InA_In_eq in_map_iff.
  firstorder eauto.
  - exists cl; split => //. unfold ClausesProp.to_list. now eapply Clauses_In_elements.
  - eapply Clauses_In_elements in H0. apply succ_clause_inj in H. now subst.
Qed.

Variant in_pred_closure cls : clause -> Prop :=
| incls cl n : Clauses.In cl cls -> in_pred_closure cls (add_clause n cl)
| predcl x k : in_pred_closure cls (singleton (x, k + 1)%nat, (x, k)).
Derive Signature for in_pred_closure.

Inductive entails (cls : clauses) : clause -> Prop :=
| clause_in (prems : nonEmptyLevelExprSet) (concl : LevelExpr.t) : LevelExprSet.In concl prems -> entails cls (prems, concl)
| clause_cut prems' concl' prems concl :
  in_pred_closure cls (prems', concl') ->
  entails cls (add concl' prems, concl) ->
  LevelExprSet.Subset prems' prems ->
  entails cls (prems, concl).

Definition entails_all cls (prems concls : nonEmptyLevelExprSet) :=
  LevelExprSet.For_all (fun le => entails cls (prems, le)) concls.

Notation " cls ⊢ prems → concl " := (entails cls (prems, concl)) (at level 20).
Notation " cls ⊢a prems → concl " := (entails_all cls prems concl) (at level 20).

Lemma in_pred_closure_equal cls (prems prems' : nonEmptyLevelExprSet) concl :
  LevelExprSet.Equal prems prems' ->
  in_pred_closure cls (prems, concl) -> in_pred_closure cls (prems', concl).
Proof.
  intros eq. apply NonEmptySetFacts.eq_univ' in eq. now subst prems.
Qed.

Lemma entails_equal cls (prems prems' : nonEmptyLevelExprSet) concl :
  LevelExprSet.Equal prems prems' ->
  entails cls (prems, concl) -> entails cls (prems', concl).
Proof.
  intros he en.
  replace prems' with prems => //.
  now apply eq_univ'.
Qed.

Lemma entails_plus cls c : entails cls c -> entails (succ_clauses cls) (succ_clause c).
Proof.
  induction 1.
  - constructor. apply map_spec. exists concl0. split => //.
  - eapply clause_cut with (succ_prems prems') (succ_expr concl').
    + depelim H.
      * have -> : (succ_prems prems', succ_expr concl') = add_clause n (succ_clause cl).
        { destruct cl as [prems'' concl'']. cbn in H0. noconf H0.
          rewrite add_prems_add_prems add_expr_add_expr add_clause_add_clause.
          now rewrite Nat.add_1_r. }
        constructor. now rewrite -succ_clauses_spec.
      * have eq : (succ_prems (singleton (x, (k + 1)%nat))) = (singleton (x, k + 1 + 1)%nat).
        { apply eq_univ'. unfold succ_prems.
          intros le. rewrite map_spec LevelExprSet.singleton_spec.
          split.
          { intros [? [hin ->]].
            rewrite LevelExprSet.singleton_spec in hin. red in hin; subst x0.
            reflexivity. }
          { unfold LevelExprSet.E.eq. intros ->.
            exists (x, k + 1)%nat. split.
            now rewrite LevelExprSet.singleton_spec. reflexivity. } }
        rewrite eq. constructor 2.
    + unfold succ_clause in IHentails.
      eapply entails_equal; tea.
      intros x. rewrite /succ_prems. rewrite map_spec add_spec.
      setoid_rewrite add_spec. rewrite map_spec.
      firstorder eauto. subst. now left.
    + intros x. rewrite /succ_prems !map_spec.
      intros [e [hin ->]]. exists e. firstorder.
Qed.


Derive Signature for entails.

Open Scope nat_scope.
Lemma entails_pred_closure {cls prems concl k} :
  cls ⊢ prems → (concl, 1 + k) -> cls ⊢ prems → (concl, k).
Proof.
  intros he.
  depind he.
  - eapply clause_cut.
    constructor.
    2:{ intros l hin. rewrite LevelExprSet.singleton_spec in hin. red in hin; subst l. rewrite Nat.add_1_r; exact H. }
    constructor.
    rewrite LevelExprSet.add_spec. lesets.
  - eapply clause_cut; tea.
Qed.

Lemma entails_pred_closure_n {cls prems concl k n} :
  entails cls (prems, (concl, k + n)) -> entails cls (prems, (concl, k)).
Proof.
  induction n in k |- *.
  - rewrite Nat.add_0_r. tauto.
  - intros hen. rewrite Nat.add_succ_r in hen.
    eapply IHn. now eapply entails_pred_closure in hen.
Qed.

Lemma add_clause_0 cl : add_clause 0 cl = cl.
Proof.
  destruct cl as [prems [concl k]]; cbn.
  f_equal. 2:now rewrite Nat.add_0_r.
  unfold add_prems.
  eapply eq_univ'. intros [l k'].
  rewrite NonEmptySetFacts.map_spec.
  unfold add_expr. firstorder. destruct x. noconf H0.
  now rewrite Nat.add_0_r.
Qed.

Lemma incls0 {cls cl} : Clauses.In cl cls -> in_pred_closure cls cl.
Proof.
  intros hin.
  have hcl := incls _ _ 0 hin.
  now rewrite add_clause_0 in hcl.
Qed.

Lemma entails_in {cls cl} : Clauses.In cl cls -> entails cls cl.
Proof.
  intros hin.
  destruct cl as [prems concl].
  eapply clause_cut.
  - now eapply incls0.
  - constructor. eapply LevelExprSet.add_spec. now left.
  - reflexivity.
Qed.



Lemma in_pred_closure_shift {cls cl} n : in_pred_closure cls cl -> in_pred_closure cls (add_clause n cl).
Proof.
  destruct 1.
  - rewrite add_clause_add_clause. now constructor.
  - cbn. eapply in_pred_closure_equal with (singleton (x, k + 1 + n)).
    { intros le. rewrite In_add_prems; rewrite_strat (topdown LevelExprSet.singleton_spec).
      intuition auto. exists (x, k + 1). split => //.
      now destruct H as [le' [-> ->]]. }
    rewrite -Nat.add_assoc. rewrite -[1 + _](Nat.add_1_r n)  Nat.add_assoc. constructor.
Qed.

Lemma add_clause_singleton n le concl k : add_clause n (singleton le, (concl, k)) = (singleton (add_expr n le), (concl, k + n)).
Proof.
  rewrite /add_clause //=. f_equal.
  apply eq_univ'. intros le'. rewrite In_add_prems.
  rewrite_strat (topdown LevelExprSet.singleton_spec).
  unfold LevelExprSet.E.eq. firstorder. subst. reflexivity.
Qed.

Lemma entails_shift {cls cl} n : entails cls cl -> entails cls (add_clause n cl).
Proof.
  induction 1.
  - unfold add_clause. constructor.
    rewrite In_add_prems. exists concl0. split => //.
  - eapply (clause_cut _ (add_prems n prems') (add_expr n concl')).
    2:{ unfold add_clause in *. eapply entails_equal; tea.
    intros le. setoid_rewrite In_add_prems. setoid_rewrite LevelExprSet.add_spec.
    setoid_rewrite In_add_prems.
    unfold LevelExprSet.E.eq. firstorder. subst. now left. }
    2:{ intros x. rewrite !In_add_prems. firstorder. }
    eapply (in_pred_closure_shift _ H).
Qed.

Lemma entails_subset cls (prems prems' : nonEmptyLevelExprSet) concl : LevelExprSet.Subset prems prems' ->
  entails cls (prems, concl) ->
  entails cls (prems', concl).
Proof.
  intros hsubt.
  intros H; revert prems' hsubt; depind H.
  - constructor. eapply hsubt, H.
  - intros prems'' hsub.
    eapply clause_cut. 2:eapply IHentails. tea.
    2:lesets. intros x; rewrite !LevelExprSet.add_spec. firstorder.
Qed.

Lemma entails_trans {cls prems concl concl'} :
  entails cls (prems, concl) ->
  entails cls (singleton concl, concl') ->
  entails cls (prems, concl').
Proof.
  intros H; depind H.
  - intros he.
    depelim he.
    * rewrite LevelExprSet.singleton_spec in H0. red in H0; subst concl0.
      now constructor.
    * eapply (clause_cut _ prems'). tea.
      eapply entails_subset; tea.
      intros ?; rewrite !LevelExprSet.add_spec LevelExprSet.singleton_spec; firstorder.
      red in H2; subst a. now right. intros x. firstorder. apply H1 in H2.
      rewrite LevelExprSet.singleton_spec in H2. now red in H2; subst x.
  - intros he.
    specialize (IHentails concl'0 he).
    eapply clause_cut; tea.
Qed.

Lemma entails_weak {cls prem concl concl'} :
  entails cls (prem, concl) ->
  entails cls (add concl' prem, concl).
Proof.
  intros H. depind H.
  - constructor. apply LevelExprSet.add_spec. now right.
  - eapply (clause_cut _ _ concl'); tea.
    rewrite add_comm. apply IHentails.
    intros x; rewrite LevelExprSet.add_spec. firstorder.
Qed.

Lemma entails_weak_union {cls prem concl concl'} :
  entails cls (prem, concl) ->
  entails cls (univ_union concl' prem, concl).
Proof.
  intros hyp.
  move: concl'.
  apply: nonEmptyLevelExprSet_elim.
  - intros le. rewrite univ_union_comm univ_union_add_singleton.
    now apply entails_weak.
  - intros le prems ih.
    rewrite univ_union_add_distr.
    now eapply entails_weak.
Qed.

Lemma entails_all_weak {cls prem concl concl'} :
  entails_all cls prem concl ->
  entails_all cls (add concl' prem) concl.
Proof.
  intros hcl x hin.
  specialize (hcl _ hin). cbn in hcl.
  now apply entails_weak.
Qed.

Lemma entails_all_weak_union {cls prem concl concl'} :
  entails_all cls prem concl ->
  entails_all cls (univ_union concl' prem) concl.
Proof.
  intros hcl x hin.
  specialize (hcl _ hin). cbn in hcl.
  now apply entails_weak_union.
Qed.

Lemma entails_all_weak' {cls prem concl concl'} :
  entails_all cls prem concl ->
  entails_all cls (add concl' prem) (add concl' concl).
Proof.
  intros hcl x hin.
  eapply LevelExprSet.add_spec in hin as []. red in H; subst.
  - constructor. eapply LevelExprSet.add_spec. now left.
  - specialize (hcl _ H). cbn in hcl.
    now apply entails_weak.
Qed.

Lemma entails_cut_all {cls prems' concl' prems concls} :
  in_pred_closure cls (prems', concl') ->
  cls ⊢a add concl' prems → concls ->
  prems' ⊂_leset prems ->
  cls ⊢a prems → concls.
Proof.
  intros inp he hp x hin.
  eapply clause_cut; tea.
  now apply he in hin.
Qed.

Lemma entails_all_subset {cls} {prems prems' prems'' : nonEmptyLevelExprSet} :
  prems'' ⊂_leset prems' ->
  cls ⊢a prems → prems' ->
  cls ⊢a prems → prems''.
Proof.
  intros incl ha x hin.
  eapply incl in hin. now apply ha in hin.
Qed.

(* Lemma entails_all_one {cls prems concl concl'} :
  entails_all cls prems concl ->
  entails cls (univ_union concl prems, concl') ->
  entails cls (prems, concl').
Proof.
  intros hall he; depind he.
  - eapply LevelExprSet.union_spec in H as [].
    2:now constructor.
    now eapply hall in H.
  - eapply clause_cut in he; tea. 3:reflexivity. specialize (IHhe _ _ concl0 hall). *)

Lemma entails_all_add cls prem l prems' :
  cls ⊢a prem → add l prems' <->
  cls ⊢ prem → l /\ cls ⊢a prem → prems'.
Proof.
  rewrite /entails_all /LevelExprSet.For_all.
  setoid_rewrite LevelExprSet.add_spec; rewrite /LevelExprSet.E.eq.
  firstorder. now subst.
Qed.

Lemma entails_add {cls prems cl concl} :
  entails cls (prems, cl) ->
  entails cls (add cl prems, concl) ->
  entails cls (prems, concl).
Proof.
  intros H; depind H.
  - intros he.
    depelim he.
    * rewrite LevelExprSet.add_spec in H0. destruct H0 as [].
      { red in H0; subst concl0. now constructor. }
      { now constructor. }
    * have eq : prems = add concl0 prems.
      { eapply eq_univ'. intros x; rewrite LevelExprSet.add_spec. firstorder. now red in H2; subst. }
      rewrite -eq in H1.
      eapply (clause_cut _ prems' _ prems). tea. 2:tea.
      now rewrite -eq in he.
  - intros he.
    eapply clause_cut. tea. eapply IHentails.
    rewrite add_comm. now eapply entails_weak.
    exact H1.
Qed.

Lemma entails_cumul_one {cls prems prems' concl} :
  entails_all cls prems prems' ->
  entails cls (univ_union prems prems', concl) ->
  entails cls (prems, concl).
Proof.
  revert prems' prems concl.
  apply: nonEmptyLevelExprSet_elim.
  - intros. specialize (H le). forward H by now apply LevelExprSet.singleton_spec.
    cbn in H.
    eapply entails_add; tea.
    now rewrite -univ_union_add_singleton.
  - intros le prems ih prem concl' hadd hadd'.
    rewrite univ_union_comm univ_union_add_distr -univ_union_comm -univ_union_add_distr in hadd'.
    eapply ih in hadd'. 2:{ apply entails_all_weak. apply entails_all_add in hadd as []. exact H0. }
    apply entails_all_add in hadd as [].
    eapply entails_add; tea.
Qed.

Lemma entails_all_cumul {cls prems prems' concl} :
  entails_all cls prems prems' ->
  entails_all cls (univ_union prems prems') concl ->
  entails_all cls prems concl.
Proof.
  intros hp hc.
  intros x hin. apply hc in hin.
  eapply entails_cumul_one; tea.
Qed.

Lemma entails_all_one {cls prem concl concl'} :
  entails_all cls prem concl ->
  entails cls (concl, concl') ->
  entails cls (prem, concl').
Proof.
  intros ha he.
  eapply entails_cumul_one; tea.
  now eapply entails_weak_union.
Qed.

Lemma entails_all_trans {cls prem concl concl'} :
  entails_all cls prem concl ->
  entails_all cls concl concl' ->
  entails_all cls prem concl'.
Proof.
  intros ha he cl hin.
  apply he in hin.
  eapply entails_all_one; tea.
Qed.

Lemma entails_incr_shift cls concl k n : entails cls (singleton (concl, k), (concl, k + 1)) ->
  entails cls (singleton (concl, k), (concl, k + 1 + n)).
Proof.
  induction n in k |- *; auto.
  - now rewrite Nat.add_0_r.
  - intros en.
    have hs := entails_shift 1 en. rewrite add_clause_singleton /= in hs.
    apply IHn in hs.
    rewrite -Nat.add_assoc Nat.add_1_l in hs.
    now eapply entails_trans.
Qed.

Lemma entails_incr_all cls concl k : entails cls (singleton (concl, k), (concl, k + 1)) ->
  forall k', entails cls (singleton (concl, k), (concl, k')).
Proof.
  intros en k'.
  destruct (Nat.lt_trichotomy k k') as [|[]]; subst; auto.
  - eapply (entails_incr_shift _ _ _ (k' - k - 1)) in en.
    assert (k + 1 + (k' - k - 1) = k') by lia. now rewrite H0 in en.
  - constructor. now rewrite LevelExprSet.singleton_spec.
  - have [k0 ->] : (exists kd, k = k' + kd). { exists (k - k'). lia. }
    eapply (entails_pred_closure_n (n:=k0)). constructor. now apply LevelExprSet.singleton_spec.
Qed.

Lemma entails_all_concl_union {cls prems concl concl'} :
  cls ⊢a prems → concl ->
  cls ⊢a prems → concl' ->
  cls ⊢a prems → univ_union concl concl'.
Proof.
  intros l r.
  rewrite /entails_all.
  intros x. rewrite univ_union_spec. intros []. now apply l. now apply r.
Qed.

Lemma entails_all_union {cls prems concl prems' concl'} :
  cls ⊢a prems → concl ->
  cls ⊢a prems' → concl' ->
  cls ⊢a univ_union prems prems' → univ_union concl concl'.
Proof.
  intros l r.
  apply entails_all_concl_union.
  rewrite univ_union_comm.
  now eapply entails_all_weak_union.
  now eapply entails_all_weak_union.
Qed.


Lemma entails_all_shift {cls : clauses} {prems concl : univ} (n : nat) :
  cls ⊢a prems → concl ->
  cls ⊢a add_prems n prems → add_prems n concl.
Proof.
  intros cla cl.
  rewrite In_add_prems => [[le' [hin ->]]].
  eapply (entails_shift (cl := (prems, le'))).
  now apply cla in hin.
Qed.

Lemma in_pred_closure_subset {cls cls' prems concl} :
  in_pred_closure cls (prems, concl) ->
  cls ⊂_clset cls' ->
  in_pred_closure cls' (prems, concl).
Proof.
  induction 1.
  - move/(_ _ H). now constructor.
  - constructor.
Qed.

Lemma entails_clauses_subset cls cls' prems concl :
  cls ⊢ prems → concl ->
  cls ⊂_clset cls' ->
  cls' ⊢ prems → concl.
Proof.
  induction 1 in cls' |- * => incl.
  - now constructor.
  - eapply clause_cut.
    + eapply in_pred_closure_subset; tea.
    + now apply IHentails.
    + assumption.
Qed.

Lemma entails_all_clauses_subset cls cls' prems concl :
  cls ⊢a prems → concl ->
  cls ⊂_clset cls' ->
  cls' ⊢a prems → concl.
Proof.
  intros d incl [l k].
  now move/d/entails_clauses_subset.
Qed.


Definition to_clauses (prems : nonEmptyLevelExprSet) (concl : nonEmptyLevelExprSet) : clauses :=
  LevelExprSet.fold (fun lk cls => Clauses.add (prems, lk) cls) concl Clauses.empty.

Definition is_loop (cls : clauses) (t : nonEmptyLevelExprSet) :=
  let cls' := to_clauses t (succ_prems t) in
  Clauses.For_all (fun cl' => entails cls cl') cls'.

(* Definition is_looping (w : LevelSet.t) n (cls : clauses) :=
  let preml := LevelSet.elements w in
  let prem := List.map (fun e => (e, n)) preml in
  is_loop cls prem. *)

Definition levelexprset_of_levels (ls : LevelSet.t) n : LevelExprSet.t :=
  LevelSet.fold (fun x => LevelExprSet.add (x, n)) ls LevelExprSet.empty.

Lemma levelexprset_of_levels_spec {ls : LevelSet.t} {l k n} :
  LevelExprSet.In (l, k) (levelexprset_of_levels ls n) <-> LevelSet.In l ls /\ k = n.
Proof.
  rewrite /levelexprset_of_levels.
  eapply LevelSetProp.fold_rec.
  - intros s' he. rewrite LevelExprSetFact.empty_iff. firstorder.
  - intros x a s' s'' hin hnin hadd ih.
    rewrite LevelExprSet.add_spec; unfold LevelExprSet.E.eq.
    firstorder eauto; try noconf H1 => //.
    apply hadd in H1. firstorder. subst. now left.
Qed.

#[program]
Definition of_level_set (ls : LevelSet.t) n (hne : ~ LevelSet.Empty ls) : nonEmptyLevelExprSet :=
  {| t_set := levelexprset_of_levels ls n |}.
Next Obligation.
  apply not_Empty_is_empty => he. apply hne.
  intros l nin. specialize (he (l,n)). apply he.
  now rewrite levelexprset_of_levels_spec.
Qed.

Definition loop_on_univ cls u := cls ⊢a u → succ_prems u.

(* Definition loop_on W (hne : ~ LevelSet.Empty W) n cls :=
  cls ⊢a of_level_set W n hne → of_level_set W (n + 1) hne.

Lemma loop_on_proper W W' n hne' cls : W =_lset W' -> exists hne, loop_on W hne n cls -> loop_on W' hne' n cls.
Proof.
  intros eq; rewrite /loop_on /loop_on_univ.
  assert (hne : ~ LevelSet.Empty W). now rewrite eq.
  exists hne.
  assert (of_level_set W n hne = of_level_set W' n hne') as ->.
  apply eq_univ'. unfold of_level_set; cbn. intros []. rewrite !levelexprset_of_levels_spec. now rewrite eq.
  assert (of_level_set W (n + 1) hne = of_level_set W' (n + 1) hne') as ->.
  apply eq_univ'. unfold of_level_set; cbn. intros []. rewrite !levelexprset_of_levels_spec. now rewrite eq.
  by [].
Qed. *)

Lemma loop_on_subset {cls cls' u} : Clauses.Subset cls cls' -> loop_on_univ cls u -> loop_on_univ cls' u.
Proof.
  intros sub; rewrite /loop_on_univ => hyp.
  now eapply entails_all_clauses_subset.
Qed.

Inductive result (V U : LevelSet.t) (cls : clauses) (m : model) :=
  | Loop (v : univ) (islooping : loop_on_univ cls v)
  | Model (w : LevelSet.t) (m : valid_model V w m cls) (prf : U ⊂_lset w).
Arguments Loop {V U cls m}.
Arguments Model {V U cls m}.
Arguments lexprod {A B}.

Definition option_of_result {V U m cls} (r : result V U m cls) : option model :=
  match r with
  | Model w m _ => Some m.(model_model)
  | Loop v _ => None
  end.

Notation "#| V |" := (LevelSet.cardinal V).

Notation loop_measure V W := (#|V|, #|V| - #|W|)%nat.

Definition lexprod_rel := lexprod lt lt.

#[local] Instance lexprod_rel_wf : WellFounded lexprod_rel.
Proof.
  eapply (Acc_intro_generator 1000). unfold lexprod_rel. eapply wf_lexprod, lt_wf. eapply lt_wf.
Defined.

Lemma strictly_updates_trans {cls cls' W W' m m' m''} :
    strictly_updates cls W m m' ->
    strictly_updates cls' W' m' m'' ->
    strictly_updates (Clauses.union cls cls') (LevelSet.union W W') m m''.
  Proof.
    intros su su'.
    eapply update_trans; eapply strictly_updates_weaken; tea; clsets.
  Qed.

Lemma check_model_is_update_of {cls cls' U W minit m m'} : is_update_of cls U minit m -> check_model cls' (U, m) = Some (W, m') ->
  strictly_updates (Clauses.union cls cls') W minit m' /\ U ⊂_lset W.
Proof.
  rewrite /is_update_of.
  destruct LevelSet.is_empty eqn:he.
  - intros ->. eapply LevelSetFact.is_empty_2 in he.
    eapply LevelSetProp.empty_is_empty_1 in he.
    eapply LevelSet.eq_leibniz in he. rewrite he.
    move/check_model_updates_spec_empty. intros H; split => //. 2:lsets.
    eapply strictly_updates_weaken; tea. clsets.
  - intros hs. move/check_model_spec => [w'' [su ->]]. split; [|lsets].
    eapply strictly_updates_trans; tea.
Qed.

Lemma is_update_of_case cls W m m' :
  is_update_of cls W m m' ->
  (LevelSet.Empty W /\ m =m m') \/ strictly_updates cls W m m'.
Proof.
  rewrite /is_update_of.
  destruct LevelSet.is_empty eqn:he.
  - intros ->. left => //. now eapply LevelSetFact.is_empty_2 in he.
  - intros H; now right.
Qed.


Lemma model_incl {V W m cls} : valid_model V W m cls -> W ⊂_lset V.
Proof.
  intros vm; have upd := model_updates vm.
  move/is_update_of_case: upd => [].
  - intros [ne eq]. lsets.
  - move/strictly_updates_incl. have hv := model_clauses_conclusions vm. lsets.
Qed.

(*
        model_of_W : model_of W model_model;
    model_incl : ;
model_extends : model_extension V m model_model;

Arguments model_of_W {V W m cls}.
Arguments model_incl {V W m cls}.
Arguments model_extends {V W m cls}.
 *)

Lemma model_of_ext {W m m'} :
  model_of W m -> m ⩽ m' -> model_of W m'.
Proof.
  intros mof ext.
  intros k hin. destruct (mof k hin). specialize (ext _ _ H) as [k' []]. now exists k'.
Qed.

Lemma valid_model_total W W' m cls :
  forall vm : valid_model W W' m cls, model_of W m -> model_of W (model_model vm).
Proof.
  intros []; cbn => htot.
  move/is_update_of_case: model_updates0 => [].
  - intros [ne eq] => //.
  - intros su. eapply strictly_updates_ext in su.
    eapply model_of_ext; tea.
Qed.

Lemma is_update_of_ext {cls W m m'} : is_update_of cls W m m' -> m ⩽ m'.
Proof.
  move/is_update_of_case => [].
  - intros [he%LevelSetProp.empty_is_empty_1]. red. setoid_rewrite H. firstorder.
  - apply strictly_updates_ext.
Qed.

Lemma model_of_union {U V cls} : model_of U cls -> model_of V cls -> model_of (LevelSet.union U V) cls.
Proof.
  intros hu hv x.
  rewrite LevelSet.union_spec; move => [] hin.
  now apply hu. now apply hv.
Qed.

Lemma model_of_union_inv U V cls : model_of (LevelSet.union U V) cls -> model_of U cls /\ model_of V cls.
Proof.
  rewrite /model_of.
  setoid_rewrite LevelSet.union_spec. firstorder.
Qed.

Lemma strictly_updates_model_of_gen cls W m m' :
  strictly_updates cls W m m' ->
  forall W', model_of W' m -> model_of (LevelSet.union W' W) m'.
Proof.
  clear.
  induction 1.
  - intros W' tot x.
    destruct cl as [prems [concl cl]].
    destruct H0 as [minv [hmin ? ? heq]]. setoid_rewrite heq.
    setoid_rewrite LevelMapFact.F.add_in_iff. cbn.
    destruct (Level.eq_dec concl x).
    { now left. }
    { rewrite LevelSet.union_spec; intros [hin|hin].
      { eapply tot in hin as [wit mt]. right; exists wit. assumption. }
      { eapply LevelSet.singleton_spec in hin. red in hin; subst. congruence. } }
  - intros W' tot.
    eapply IHstrictly_updates1 in tot. eapply IHstrictly_updates2 in tot.
    eapply model_of_subset; tea. intros x; lsets.
Qed.


Lemma model_of_empty m : model_of LevelSet.empty m.
Proof. intros x; now move/LevelSet.empty_spec. Qed.

Instance model_of_proper : Proper (LevelSet.Equal ==> LevelMap.Equal ==> iff) model_of.
Proof.
  intros ? ? H ? ? H'. unfold model_of. setoid_rewrite H.
  now setoid_rewrite H'.
Qed.

Lemma strictly_updates_total_model {cls W m m'} :
  strictly_updates cls W m m' ->
  model_of W m'.
Proof.
  move/strictly_updates_model_of_gen/(_ LevelSet.empty).
  intros H. forward H. apply model_of_empty.
  rewrite LevelSetProp.empty_union_1 in H => //. lsets.
Qed.

Lemma strictly_updates_only_model_gen cls W m m' :
  strictly_updates cls W m m' ->
  forall W', only_model_of W' m -> only_model_of (LevelSet.union W' W) m'.
Proof.
  clear.
  induction 1.
  - intros W' tot x.
    destruct cl as [prems [concl cl]].
    destruct H0 as [minv [hmin ? ? heq]]. setoid_rewrite heq.
    setoid_rewrite LevelMapFact.F.add_mapsto_iff. cbn.
    destruct (Level.eq_dec concl x).
    { subst. rewrite LevelSet.union_spec LevelSet.singleton_spec.
      firstorder; exists (cl + Z.to_nat minv)%nat; left; split => //. }
    { rewrite LevelSet.union_spec LevelSet.singleton_spec /LevelSet.E.eq.
      firstorder. subst x. congruence. }
  - intros W' tot.
    eapply IHstrictly_updates1 in tot. eapply IHstrictly_updates2 in tot.
    eapply only_model_of_eq; tea. intros x; lsets.
Qed.

Lemma is_update_of_total_model cls W m m' : is_update_of cls W m m' -> model_of W m'.
Proof.
  move/is_update_of_case => [].
  - intros [he eq].
    rewrite /model_of. lsets.
  - eapply strictly_updates_total_model.
Qed.

Lemma strict_update_modify m cl m' : strict_update m cl m' ->
  exists k, LevelMap.Equal m' (LevelMap.add (clause_conclusion cl) k m).
Proof.
  rewrite /strict_update.
  destruct cl as [prems [concl k]].
  intros [v [hmin hlt hab eq]]. now exists (k + Z.to_nat v)%nat.
Qed.

Lemma strictly_updates_model_of {cls W m m'} :
  strictly_updates cls W m m' -> model_of W m'.
Proof.
  move/strictly_updates_model_of_gen/(_ LevelSet.empty).
  rewrite LevelSetProp.empty_union_1. lsets.
  intros H; apply H. apply model_of_empty.
Qed.

Lemma strictly_updates_modify {cls W m m'} :
  strictly_updates cls W m m' ->
  forall l k, LevelMap.MapsTo l k m' -> LevelSet.In l W \/ LevelMap.MapsTo l k m.
Proof.
  induction 1.
  + eapply strict_update_modify in H0 as [k eq].
    intros l k'. rewrite LevelSet.singleton_spec.
    rewrite eq.
    rewrite LevelMapFact.F.add_mapsto_iff.
    intros [[]|] => //. red in H0; subst.
    left. lsets. now right.
  + intros. eapply IHstrictly_updates2 in H1.
    destruct H1. left; lsets.
    eapply IHstrictly_updates1 in H1 as []. left; lsets.
    now right.
Qed.

Lemma strictly_updates_modify_inv {cls W m m'} :
  strictly_updates cls W m m' ->
  forall l k, LevelMap.MapsTo l k m -> LevelSet.In l W \/ LevelMap.MapsTo l k m'.
Proof.
  induction 1.
  + eapply strict_update_modify in H0 as [k eq].
    intros l k'. rewrite LevelSet.singleton_spec.
    rewrite eq.
    rewrite LevelMapFact.F.add_mapsto_iff.
    intros hm. unfold Level.eq.
    destruct (eq_dec l (clause_conclusion cl)). subst. now left.
    right. right. auto.
  + intros. eapply IHstrictly_updates1 in H1 as [].
    left; lsets.
    eapply IHstrictly_updates2 in H1 as []. left; lsets.
    now right.
Qed.

Lemma strictly_updates_outside cls W m m' :
  strictly_updates cls W m m' -> model_map_outside W m m'.
Proof.
  move=> su.
  have lr := strictly_updates_modify su.
  have rl := strictly_updates_modify_inv su.
  intros l nin k.
  split; intros.
  - apply rl in H as [] => //.
  - apply lr in H as [] => //.
Qed.

Lemma valid_model_model_map_outside {W W' m cls} (vm : valid_model W W' m cls) : model_map_outside W m (model_model vm).
Proof.
  destruct vm as [m' mV mupd mcls mok]; cbn.
  - move/is_update_of_case: mupd => [].
    * intros [ne <-]. red. intros. reflexivity.
    * intros su. eapply (model_map_outside_weaken (W:=W')).
      2:{ eapply strictly_updates_incl in su. lsets. }
      clear -su. revert su.
      eapply strictly_updates_outside.
Qed.


Lemma check_model_has_invariants {cls w m w' m'} :
  model_of (clauses_conclusions cls) m ->
  model_of w m ->
  check_model cls (w, m) = Some (w', m') ->
  check_model_invariants cls w m w' m' true.
Proof.
  intros mof tot.
  move/check_model_spec => [w'' [su ->]].
  cbn. split.
  - lsets.
  - apply strictly_updates_incl in su. lsets.
  - clear -su. induction su.
    * exists cl. split => //. now eapply strict_update_invalid.
    unfold clause_conclusion. lsets.
    destruct cl as [prems [concl k]].
    destruct H0 as [minp [hin hlt hnabove habove]].
    move: hnabove habove. rewrite /level_value_above.
    cbn. destruct level_value eqn:hv => //; try constructor.
    intros hle. intros ->. rewrite level_value_add. constructor.
    move/negbTE: hle. lia.
    * destruct IHsu1 as [cl []].
      exists cl. split => //. lsets.
      apply strictly_updates_ext in su2.
      depelim H2; rewrite ?H3. 2:{ rewrite H2; constructor. }
      eapply level_value_MapsTo', su2 in H4 as [k' [map le]].
      eapply level_value_MapsTo in map. rewrite map. constructor; lia.
  - constructor. now eapply strictly_updates_ext.
    clear -mof su.
    induction su.
    * move: H0; unfold strict_update. destruct cl as [prems [concl k]].
      intros [v [hmi hlt nabove eqm]]. intros l. rewrite eqm.
      rewrite LevelMapFact.F.add_in_iff. specialize (mof l).
      rewrite clauses_conclusions_spec in mof. firstorder.
    * specialize (IHsu1 mof). transitivity m' => //.
      apply IHsu2. intros l hin. specialize (mof _ hin). now apply IHsu1 in mof.
    * eapply model_map_outside_weaken. now eapply strictly_updates_outside. lsets.
  - eapply strictly_updates_model_of_gen in su; tea.
Qed.

Lemma clauses_levels_conclusions cls V : clauses_levels cls ⊂_lset V ->
  clauses_conclusions cls ⊂_lset V.
Proof.
  intros hin x; rewrite clauses_conclusions_spec; move => [cl [hin' eq]]; apply hin.
  rewrite clauses_levels_spec. exists cl. split => //. subst x.
  rewrite clause_levels_spec. now right.
Qed.
Definition clauses_premises_levels (cls : clauses) : LevelSet.t :=
  Clauses.fold (fun cl acc => LevelSet.union (levels (premise cl)) acc) cls LevelSet.empty.

Lemma clauses_premises_levels_spec_aux l cls acc :
  LevelSet.In l (Clauses.fold (fun cl acc => LevelSet.union (levels (premise cl)) acc) cls acc) <->
  (exists cl, Clauses.In cl cls /\ LevelSet.In l (levels (premise cl))) \/ LevelSet.In l acc.
Proof.
  eapply ClausesProp.fold_rec.
  - intros.
    intuition auto. destruct H1 as [k [hin hl]]. clsets.
  - intros x a s' s'' hin nin hadd ih.
    rewrite LevelSet.union_spec.
    split.
    * intros [hin'|].
      left. exists x. split => //.
      apply hadd. now left.
      apply ih in H.
      intuition auto.
      left. destruct H0 as [k Hk]. exists k. intuition auto. apply hadd. now right.
    * intros [[k [ins'' ?]]|inacc].
      eapply hadd in ins''. destruct ins''; subst.
      + now left.
      + right. apply ih. now left; exists k.
      + right. intuition auto.
Qed.

Lemma clauses_premises_levels_spec l cls :
  LevelSet.In l (clauses_premises_levels cls) <->
  exists cl, Clauses.In cl cls /\ LevelSet.In l (levels (premise cl)).
Proof.
  unfold clauses_premises_levels.
  rewrite clauses_premises_levels_spec_aux.
  intuition auto. lsets.
Qed.

Lemma clauses_levels_premises cls V : clauses_levels cls ⊂_lset V ->
  clauses_premises_levels cls ⊂_lset V.
Proof.
  intros hin x; rewrite clauses_premises_levels_spec; move => [cl [hin' eq]]; apply hin.
  rewrite clauses_levels_spec. exists cl. split => //.
  rewrite clause_levels_spec. now left.
Qed.

Lemma clauses_premises_levels_incl cls : clauses_premises_levels cls ⊂_lset clauses_levels cls.
Proof.
  intros x; rewrite clauses_premises_levels_spec clauses_levels_spec; move => [cl [hin' eq]].
  exists cl; split => //.
  rewrite clause_levels_spec. now left.
Qed.

Lemma clauses_premises_levels_mon {cls cls'} : cls ⊂_clset cls' ->
  clauses_premises_levels cls ⊂_lset clauses_premises_levels cls'.
Proof.
  intros hin x; rewrite !clauses_premises_levels_spec; move => [cl [hin' eq]].
  exists cl; split => //. now apply hin.
Qed.

Definition monotone_selector sel :=
  forall cls' cls, cls' ⊂_clset cls -> sel cls' ⊂_lset sel cls.

Lemma clauses_levels_mon : monotone_selector clauses_levels.
Proof.
  intros cls' cls hin x; rewrite !clauses_levels_spec; move => [cl [hin' eq]].
  exists cl; split => //. now apply hin.
Qed.

Definition infers_atom (m : model) (l : Level.t) (k : nat) := Some k ≤ level_value m l.

Definition max_premise_model cls sel m :=
  (forall l, LevelSet.In l (sel cls) ->
  LevelMap.MapsTo l (max_clause_premise cls) m) /\
  (forall l k, LevelMap.MapsTo l k m -> LevelSet.In l (sel cls) /\ k = max_clause_premise cls).


Definition max_premise_map cls : model :=
  let max := max_clause_premise cls in
  let ls := clauses_levels cls in
  LevelSet.fold (fun l acc => LevelMap.add l max acc) ls (LevelMap.empty _).

Definition above_max_premise_model cls m :=
  (exists V, strictly_updates cls V (max_premise_map cls) m) \/ m = max_premise_map cls.

Lemma max_premise_model_exists cls : max_premise_model cls clauses_levels (max_premise_map cls).
Proof.
  rewrite /max_premise_map; split.
  - intros l.
    eapply LevelSetProp.fold_rec.
    { intros s he hin. now apply he in hin. }
    intros.
    destruct (Level.eq_dec l x). subst.
    * eapply LevelMapFact.F.add_mapsto_iff. left; split => //.
    * eapply LevelMapFact.F.add_mapsto_iff. right. split => //. now unfold Level.eq. apply H2.
      specialize (H1 l). apply H1 in H3. destruct H3 => //. congruence.
  - intros l k.
    eapply LevelSetProp.fold_rec.
    { intros s' he hm. now eapply LevelMapFact.F.empty_mapsto_iff in hm. }
    intros.
    eapply LevelMapFact.F.add_mapsto_iff in H3 as [].
    * destruct H3. noconf H4. split => //. apply H1. now left.
    * destruct H3. firstorder.
Qed.

Lemma infer_atom_downward {m l k k'} :
  infers_atom m l k ->
  (k' <= k)%nat ->
  infers_atom m l k'.
Proof.
  rewrite /infers_atom.
  intros infa le.
  transitivity (Some k) => //. now constructor.
Qed.

Lemma infers_atom_le {m m' l k} :
  infers_atom m l k ->
  m ⩽ m' ->
  infers_atom m' l k.
Proof.
  rewrite /infers_atom.
  intros infa le.
  depelim infa. eapply level_value_MapsTo' in H0. eapply le in H0 as [k' [hm hle]].
  rewrite (level_value_MapsTo hm). constructor; lia.
Qed.

Lemma infers_atom_mapsto m l k : infers_atom m l k <->
  exists k', LevelMap.MapsTo l k' m /\ (k <= k')%nat.
Proof.
  rewrite /infers_atom; split.
  - intros hle; depelim hle.
    eapply level_value_MapsTo' in H0. exists y. split => //.
  - intros [k' [hm hle]].
    eapply level_value_MapsTo in hm. rewrite hm. now constructor.
Qed.

Lemma above_max_premise_model_infers {cls m} :
  above_max_premise_model cls m ->
  (forall l, LevelSet.In l (clauses_levels cls) -> infers_atom m l (max_clause_premise cls)).
Proof.
  intros ha l hl.
  have hm := max_premise_model_exists cls.
  destruct ha as [[V su]|eq].
  * eapply strictly_updates_ext in su.
    eapply infers_atom_le; tea.
    eapply infers_atom_mapsto.
    destruct hm. exists (max_clause_premise cls). split => //.
    now eapply H.
  * subst m. eapply infers_atom_mapsto. destruct hm.
    specialize (H l hl). eexists; split. exact H. lia.
Qed.

(* Lemma max_premise_model_above cls sel sel' m :
  (sel' cls ⊂_lset sel cls) ->
  max_premise_model cls sel m ->
  above_max_premise_model cls m.
Proof.
  move=> incl mp l hl; move: (proj1 mp l (incl _ hl)); rewrite /infers_atom.
  move/level_value_MapsTo => ->. reflexivity.
Qed. *)


Lemma clauses_with_concl_union cls W W' :
  Clauses.Equal (clauses_with_concl cls (LevelSet.union W W'))
    (Clauses.union (clauses_with_concl cls W) (clauses_with_concl cls W')).
Proof.
  intros x. rewrite Clauses.union_spec !in_clauses_with_concl LevelSet.union_spec.
  firstorder.
Qed.

Lemma strictly_updates_strenghten {cls W m m'} :
  strictly_updates cls W m m' ->
  strictly_updates (cls ↓ W) W m m'.
Proof.
  induction 1.
  - constructor. rewrite in_clauses_with_concl. split => //.
    eapply LevelSet.singleton_spec; reflexivity. exact H0.
  - rewrite clauses_with_concl_union. econstructor 2.
    eapply strictly_updates_weaken; tea. intros x; clsets.
    eapply strictly_updates_weaken; tea. intros x; clsets.
Qed.

Lemma clauses_with_concl_subset cls W : (cls ↓ W) ⊂_clset cls.
Proof. now intros ?; rewrite in_clauses_with_concl. Qed.

Section InnerLoop.
  Definition sum_W W (f : LevelSet.elt -> nat) : nat :=
    LevelSet.fold (fun w acc => acc + f w)%nat W 0%nat.

  Definition measure (W : LevelSet.t) (cls : clauses) (m : model) : nat :=
    sum_W W (fun w => Z.to_nat (measure_w W cls m w)).

  Lemma maps_to_value_default {x k m} : LevelMap.MapsTo x k m -> level_value m x = Some k.
  Proof.
    intros h; apply LevelMap.find_1 in h.
    now rewrite /level_value h.
  Qed.

  Lemma measure_model W cls m :
    model_of W m ->
    let clsdiff := cls_diff cls W in
    measure W cls m = 0%nat -> is_model clsdiff m.
  Proof using.
    unfold measure, sum_W, measure_w, is_model.
    set (clsdiff := Clauses.diff _ _).
    intros hv hm.
    assert (LevelSet.For_all (fun w => Some (v_minus_w_bound W m + max_gain clsdiff) ≤ level_value m w)%nat W).
    { move: hm.
      generalize (v_minus_w_bound W m) => vbound.
      eapply LevelSetProp.fold_rec.
      intros. intros x hin. firstorder eauto.
      intros x a s' s'' inw nins' hadd ih heq.
      forward ih by lia.
      intros l hin.
      specialize (hv _ inw) as [k lv]. rewrite /level_value_default (maps_to_value_default lv) in heq.
      apply hadd in hin as [].
      * subst x. rewrite (maps_to_value_default lv). constructor. lia.
      * now apply ih. }
    clear hm.
    eapply ClausesFact.for_all_iff. tc.
    intros cl hl.
    unfold valid_clause.
    destruct min_premise as [k0|] eqn:hk0 => //.
    destruct cl as [prem [l k]] => /=. cbn in hk0.
    elim: Z.ltb_spec => //= ge.
    rewrite /clsdiff in hl.
    destruct (proj1 (Clauses.diff_spec _ _ _) hl) as [hlcls hl'].
    eapply in_clauses_with_concl in hlcls as [lW incls].
    specialize (H _ lW). cbn -[clsdiff] in H. cbn in lW.
    specialize (hv _ lW) as [vl hvl]. rewrite /level_value_above (maps_to_value_default hvl).
    rewrite (maps_to_value_default hvl) in H; depelim H.
    (* etransitivity; tea. *)
    set (prem' := non_W_atoms W prem).
    assert (ne : LevelExprSet.is_empty prem' = false).
    { now eapply (non_W_atoms_ne W (prem, (l, k)) cls). }
    set (preml := {| t_set := prem'; t_ne := ne |}).
    assert (min_premise m prem ≤Z min_premise m preml).
    { eapply min_premise_subset. eapply non_W_atoms_subset. }
    (* min_i (f(x_i)-k_i) <= max_i(f(x_i)) - min(k_i) *)
    pose proof (min_premise_spec m preml) as [amin [exmin [inminpre eqminpre]]].
    rewrite hk0 in H0. depelim H0. rename y into minpreml.
    pose proof (min_premise_max_premise _ _ _ H1) as [maxpreml eqmaxp].
    pose proof (max_premise_value_spec m preml _ eqmaxp) as [amax [exmax [inmaxpre eqmaxpre]]].
    rewrite -eqmaxp in eqmaxpre.
    pose proof (premise_min_spec preml) as [apmin [expmin [inpminpre eqpminpre]]].
    assert (min_premise m preml ≤Z Some (Z.of_nat maxpreml - Z.of_nat (premise_min preml)))%Z.
    { rewrite eqminpre in H1.
      specialize (amax _ inminpre). destruct amax as [k' [lk' hk']].
      depelim hk'.
      pose proof (min_atom_value_levelexpr_value m exmin _ _ H2 lk').
      rewrite eqminpre H2. constructor. etransitivity; tea.
      rewrite eqmaxpre in eqmaxp.
      assert (expmin <= exmin)%nat. specialize (apmin _ inminpre). lia.
      unfold level_expr_elt in *. lia. }
    apply Nat.leb_le. rewrite H1 in H2. depelim H2.
    transitivity (k + (maxpreml - premise_min preml))%nat. lia.
    assert (Z.to_nat (gain (preml, (l, k))) <= max_gain clsdiff)%nat.
    { transitivity (Z.to_nat (gain (prem, (l, k)))). 2:now apply max_gain_in.
      unfold gain. cbn.
      pose proof (premise_min_subset preml prem).
      rewrite !Z2Nat.inj_sub //; try lia. rewrite !Nat2Z.id.
      forward H3. eapply non_W_atoms_subset. lia. }
    transitivity (v_minus_w_bound W m + Z.to_nat (gain (preml, (l, k))))%nat.
    2:lia.
    unfold gain. cbn -[max_premise_value premise_min].
    assert (k + (maxpreml - premise_min preml) =
      (maxpreml + k - premise_min preml))%nat as ->. lia.
    assert (maxpreml <= v_minus_w_bound W m)%nat.
    { pose proof (v_minus_w_bound_spec W m exmax).
      have [hlevels _] := (@levels_exprs_non_W_atoms W prem (levelexpr_level exmax)).
      rewrite levelexprset_levels_spec in hlevels.
      forward hlevels.
      exists exmax.2. now destruct exmax.
      rewrite LevelSet.diff_spec in hlevels.
      destruct hlevels.
      forward H4 by auto.
      rewrite eqmaxp in eqmaxpre. unfold levelexpr_value in eqmaxpre. rewrite -eqmaxpre in H4.
      now depelim H4.
      }
    lia.
  Qed.

  Lemma level_value_default_def {m x v} : level_value m x = Some v -> level_value_default m x = v.
  Proof. unfold level_value_default. now intros ->. Qed.

  Lemma w_values_ext m m' W :
    m ⩽ m' -> model_of W m -> model_of W m'.
  Proof.
    intros ext hf x hin.
    specialize (hf x hin) as [k hl].
    specialize (ext _ _ hl) as [? []].
    now exists x0.
  Qed.

  Lemma level_values_in_W m m' W x :
    model_of W m ->
    m ⩽ m' ->
    LevelSet.In x W -> level_value m x ≤ level_value m' x ->
    exists k k', level_value m x = Some k /\ level_value m' x = Some k' /\ (k <= k')%nat.
  Proof.
    intros hwv ext hin hleq.
    specialize (hwv _ hin) as x'. destruct x' as [k hl]. rewrite (maps_to_value_default hl) in hleq.
    eapply w_values_ext in hwv; tea.
    specialize (hwv _ hin) as [k' hl'].
    rewrite (maps_to_value_default hl') in hleq. depelim hleq.
    do 2 eexists. intuition eauto.
    now rewrite (maps_to_value_default hl).
    now rewrite (maps_to_value_default hl').
  Qed.

  Lemma measure_le {W cls m m'} :
    model_of W m ->
    model_map_outside W m m' ->
    m ⩽ m' ->
    (measure W cls m' <= measure W cls m)%nat.
  Proof.
    intros hwv hout hle.
    unfold measure, measure_w, sum_W.
    rewrite (v_minus_w_bound_irrel _ _ hout).
    rewrite !LevelSet.fold_spec. unfold flip.
    eapply fold_left_le; unfold flip. 2:lia.
    - intros. rewrite LevelSet_In_elements in H.
      have lexx' := (model_le_values x hle).
      eapply level_values_in_W in lexx' as [k [k' [hk [hk' leq]]]]; tea.
      erewrite !level_value_default_def; tea. lia.
  Qed.

  Lemma measure_lt {W cls m m'} :
    model_of W m ->
    model_map_outside W m m' ->
    m ⩽ m' ->
    (exists l, [/\ LevelSet.In l W, (0 < measure_w W cls m l)%Z &
     opt_le Nat.lt (level_value m l) (level_value m' l)])%Z ->
    (measure W cls m' < measure W cls m)%nat.
  Proof.
    intros hwv hout hle.
    unfold measure, measure_w, sum_W.
    rewrite (v_minus_w_bound_irrel _ _ hout).
    intros hlt.
    rewrite !LevelSet.fold_spec. unfold flip.
    eapply fold_left_ne_lt; unfold flip.
    - unfold flip. intros; lia.
    - unfold flip; intros; lia.
    - destruct hlt as [l [hin _]]. intros he. rewrite -LevelSetProp.elements_Empty in he. lsets.
    - intros. rewrite LevelSet_In_elements in H.
      have lexx' := (model_le_values x hle).
      eapply level_values_in_W in lexx' as [k [k' [hk [hk' leq]]]]; tea.
      erewrite !level_value_default_def; tea. lia.
    - intros. rewrite LevelSet_In_elements in H.
      have lexx' := (model_le_values x hle).
      eapply level_values_in_W in lexx' as [k [k' [hk [hk' leq]]]]; tea.
      erewrite !level_value_default_def; tea. lia.
    - destruct hlt as [l [hinl hbound hlev]].
      exists l. rewrite LevelSet_In_elements. split => //.
      intros acc acc' accle.
      eapply Nat.add_le_lt_mono => //.
      depelim hlev. rewrite /level_value_default ?H0 ?H1 in hbound |- *.
      lia. now eapply model_of_value_None in H; tea.
  Qed.

  Lemma is_model_equal {cls cls' m} : Clauses.Equal cls cls' -> is_model cls m -> is_model cls' m.
  Proof. now intros ->. Qed.

  Lemma union_diff_eq {cls cls'} : Clauses.Equal (Clauses.union cls (Clauses.diff cls' cls))
    (Clauses.union cls cls').
  Proof. clsets. Qed.

  Lemma union_restrict_with_concl {cls W} :
    Clauses.Equal (Clauses.union (cls ⇂ W) (cls ↓ W)) (cls ↓ W).
  Proof.
    intros cl. rewrite Clauses.union_spec.
    intuition auto.
    eapply in_clauses_with_concl.
    now eapply in_restrict_clauses in H0 as [].
  Qed.

  Lemma union_diff {cls W} :
    Clauses.Equal (Clauses.union (Clauses.diff (cls ↓ W) (cls ⇂ W)) (cls ⇂ W)) (cls ↓ W).
  Proof.
    now rewrite ClausesProp.union_sym union_diff_eq union_restrict_with_concl.
  Qed.

  Lemma union_diff_cls {cls W} :
    Clauses.Equal (Clauses.union (Clauses.diff (cls ↓ W) (cls ⇂ W)) cls) cls.
  Proof.
    intros ?. rewrite Clauses.union_spec Clauses.diff_spec in_restrict_clauses in_clauses_with_concl.
    firstorder.
  Qed.

  Lemma maps_to_level_value x (m m' : model) :
    (forall k, LevelMap.MapsTo x k m <-> LevelMap.MapsTo x k m') ->
    level_value m x = level_value m' x.
  Proof.
    intros heq.
    unfold level_value.
    destruct LevelMap.find eqn:hl.
    apply LevelMap.find_2 in hl. rewrite heq in hl.
    rewrite (LevelMap.find_1 hl) //.
    destruct (LevelMap.find x m') eqn:hl' => //.
    apply LevelMap.find_2 in hl'. rewrite -heq in hl'.
    now rewrite (LevelMap.find_1 hl') in hl.
  Qed.

  Lemma measure_Z_lt x y :
    (x < y)%Z ->
    (0 < y)%Z ->
    (Z.to_nat x < Z.to_nat y)%nat.
  Proof. intros. lia. Qed.

  Lemma sum_pos W f :
    (0 < sum_W W f)%nat ->
    exists w, LevelSet.In w W /\ (0 < f w)%nat.
  Proof.
    unfold sum_W.
    eapply LevelSetProp.fold_rec => //.
    intros. lia.
    intros.
    destruct (Nat.ltb_spec 0 a).
    - destruct (H2 H4) as [w [hin hlt]]. exists w. split => //. apply H1. now right.
    - exists x. split => //. apply H1. now left. lia.
  Qed.

  Lemma measure_pos {W cls m} :
    (0 < measure W cls m)%nat ->
    exists l, LevelSet.In l W /\ (0 < measure_w W cls m l)%Z.
  Proof.
    unfold measure.
    move/sum_pos => [w [hin hlt]].
    exists w. split => //. lia.
  Qed.

  Lemma model_of_diff cls W m :
    model_of W m -> model_of (clauses_conclusions (cls_diff cls W)) m.
  Proof.
    intros; eapply model_of_subset; tea.
    eapply clauses_conclusions_diff_left.
  Qed.
  Hint Resolve model_of_diff : core.

  Lemma check_model_spec_diff {cls w m w' m' w''} :
    model_of w m ->
    model_of w'' m ->
    let cls := (cls_diff cls w) in
    check_model cls (w'', m) = Some (w', m') ->
    [/\ w'' ⊂_lset w', w' ⊂_lset (w'' ∪ w),
      exists cl : clause,
        let cll := levelexpr_level (concl cl) in
        [/\ Clauses.In cl cls, ~~ valid_clause m cl, LevelSet.In cll w'
          & (opt_le Nat.lt (level_value m cll) (level_value m' cll))%Z]
      & model_extension w' m m'].
  Proof.
    cbn; intros mof tot cm.
    pose proof (clauses_conclusions_diff_left cls w (cls ⇂ w)).
    apply check_model_has_invariants in cm as [].
    split => //. lsets.
    eapply model_of_subset. exact mof. tea. exact tot.
  Qed.

  Lemma model_of_extension {W W' m m'} :
    model_of W m -> model_extension W' m m' -> model_of W m'.
  Proof.
    intros mof [_ dom _].
    intros k hin. apply dom. now apply mof.
  Qed.

  Lemma clauses_partition_spec {cls W allW conclW} :
    clauses_conclusions cls ⊂_lset W ->
    Clauses.partition (premise_restricted_to W) cls = (allW, conclW) ->
    (Clauses.Equal allW (cls ⇂ W)) /\
    (Clauses.Equal conclW (Clauses.diff cls (cls ⇂ W))).
  Proof.
    intros clW.
    destruct Clauses.partition eqn:eqp.
    intros [= <- <-].
    change t with (t, t0).1.
    change t0 with (t, t0).2 at 2.
    rewrite -eqp. clear t t0 eqp.
    split.
    - intros cl. rewrite Clauses.partition_spec1.
      rewrite in_restrict_clauses Clauses.filter_spec.
      rewrite /premise_restricted_to LevelSet.subset_spec. firstorder eauto.
      apply clW, clauses_conclusions_spec. now exists cl.
    - intros cl. rewrite Clauses.partition_spec2.
      rewrite Clauses.filter_spec Clauses.diff_spec.
      rewrite /premise_restricted_to. intuition auto.
      move/negbTE: H1. eapply eq_true_false_abs.
      eapply LevelSet.subset_spec.
      now eapply in_restrict_clauses in H as [].
      apply eq_true_not_negb. move/LevelSet.subset_spec => he.
      apply H1. apply in_restrict_clauses. split => //.
      apply clW, clauses_conclusions_spec. now exists cl.
  Qed.

  Lemma clauses_conclusions_eq cls W :
    clauses_conclusions cls ⊂_lset W ->
    Clauses.Equal cls (cls ↓ W).
  Proof.
    intros cl x.
    rewrite in_clauses_with_concl. intuition auto.
    apply cl, clauses_conclusions_spec. now exists x.
  Qed.

  (* Inductive inner_result (V U : LevelSet.t) (cls : clauses) (m : model) :=
  | InLoop (w : LevelSet.t) (hne : ~ LevelSet.Empty w) (islooping : loop_on w hne cls)
  | InModel (w : LevelSet.t) (m : valid_model V w m cls).
   (* (prf : U ⊂_lset w /\ w ⊂_lset V). *)
  Arguments InLoop {V U cls m}.
  Arguments InModel {V U cls m}. *)

  Lemma is_update_of_empty cls m :
    is_update_of cls LevelSet.empty m m.
  Proof.
    unfold is_update_of.
    rewrite LevelSetFact.is_empty_1 //. lsets.
  Qed.

  Lemma strictly_updates_W_eq cls W init m W' :
    LevelSet.Equal W W' ->
    strictly_updates cls W init m ->
    strictly_updates cls W' init m.
  Proof. now intros ->. Qed.

  Lemma strictly_updates_clauses_W cls cls' W init m W' :
    Clauses.Subset cls cls' ->
    LevelSet.Equal W W' ->
    strictly_updates cls W init m ->
    strictly_updates cls' W' init m.
  Proof. intros hsub ->. now apply strictly_updates_weaken. Qed.

  Lemma strictly_updates_is_update_of cls W init m cls' W' m' :
    strictly_updates cls W init m ->
    is_update_of cls' W' m m' ->
    strictly_updates (Clauses.union cls cls') (LevelSet.union W W') init m'.
  Proof.
    move=> su /is_update_of_case; intros [[empw eq]|su'].
    rewrite <- eq. eapply (strictly_updates_weaken cls). clsets.
    eapply strictly_updates_W_eq; tea. lsets.
    eapply update_trans; tea; eapply strictly_updates_weaken; tea; clsets.
  Qed.

  Definition restrict_model W (m : model) :=
    LevelMapFact.filter (fun l k => LevelSet.mem l W) m.

  Lemma restrict_model_spec W m :
    forall l k, LevelMap.MapsTo l k (restrict_model W m) <-> LevelMap.MapsTo l k m /\ LevelSet.In l W.
  Proof.
    intros l k; rewrite /restrict_model.
    now rewrite LevelMapFact.filter_iff LevelSet.mem_spec.
  Qed.

  (* Updates the entries in m with the values in m' if any *)
  Definition model_update (m m' : model) : model :=
    LevelMap.mapi (fun l k =>
      match LevelMap.find l m' with
      | Some k' => k'
      | None => k
      end) m.

  Instance model_update_proper : Proper (LevelMap.Equal ==> LevelMap.Equal ==> LevelMap.Equal) model_update.
  Proof.
    intros ? ? eq ? ? eq'.
    rewrite /model_update.
    apply LevelMapFact.F.Equal_mapsto_iff.
    intros k e.
    rewrite LevelMapFact.F.mapi_mapsto_iff. now intros ? ? ? ->.
    rewrite LevelMapFact.F.mapi_mapsto_iff. now intros ? ? ? ->.
    firstorder. exists x1. rewrite H. now rewrite -eq eq'.
    rewrite H. exists x1. now rewrite eq -eq'.
  Qed.

  Inductive findSpec l m : option nat -> Prop :=
    | inm k : LevelMap.MapsTo l k m -> findSpec l m (Some k)
    | ninm : ~ LevelMap.In l m -> findSpec l m None.

  Lemma find_spec l m : findSpec l m (LevelMap.find l m).
  Proof.
    destruct (LevelMap.find l m) eqn:heq; constructor.
    now apply LevelMap.find_2.
    now apply LevelMapFact.F.not_find_in_iff in heq.
  Qed.

  Lemma model_update_spec m m' :
    forall l k, LevelMap.MapsTo l k (model_update m m') <->
      (~ LevelMap.In l m' /\ LevelMap.MapsTo l k m) \/
      (LevelMap.MapsTo l k m' /\ LevelMap.In l m).
  Proof.
    intros l k; split.
    - unfold model_update => hl.
      eapply LevelMapFact.F.mapi_inv in hl as [a [k' [-> [eqk mt]]]].
      move: eqk; elim: (find_spec l m').
      + intros ? hm <-. right; split => //. now exists a.
      + intros nin ->. left. split => //.
    - intros [[nin hm]|[inm' inm]].
      * eapply LevelMapFact.F.mapi_mapsto_iff. now intros x y e ->.
        elim: (find_spec l m').
        + intros k0 hm'. elim nin. now exists k0.
        + intros _. exists k. split => //.
      * eapply LevelMapFact.F.mapi_mapsto_iff. now intros x y e ->.
        elim: (find_spec l m').
        + intros k0 hm'. destruct inm as [a inm]. exists a. split => //.
          now eapply LevelMapFact.F.MapsTo_fun in inm'; tea.
        + intros nin; elim nin. now exists k.
  Qed.

  Lemma model_update_restrict m W : model_update m (restrict_model W m) =m m.
  Proof.
    apply LevelMapFact.F.Equal_mapsto_iff. intros l k.
    rewrite model_update_spec.
    split => //.
    - intros [[nin hk]|[hr inm]] => //.
      now eapply restrict_model_spec in hr.
    - intros hm.
      destruct (find_spec l (restrict_model W m)).
      + right. apply restrict_model_spec in H as [hm' hw].
        split. eapply LevelMapFact.F.MapsTo_fun in hm; tea. subst. apply restrict_model_spec; split => //.
        now exists k.
      + left. split => //.
  Qed.


  Lemma min_premise_preserved {m m'} {prems : univ} :
    (forall x, LevelSet.In x (levels prems) -> level_value m x = level_value m' x) ->
    min_premise m prems = min_premise m' prems.
  Proof.
    intros hcl.
    unfold min_premise.
    funelim (to_nonempty_list prems). bang. clear H.
    rw_in levelexprset_levels_spec hcl.
    have -> : min_atom_value m e = min_atom_value m' e.
    { destruct e as [k l'].
      rewrite /min_atom_value. rewrite -hcl //.
      exists l'.
      apply LevelExprSet.elements_spec1. rewrite e0. now left. }
    have cl' : forall x, (exists k, InA eq (x, k) l) -> level_value m x = level_value m' x.
    { intros x [k ina]. apply hcl. exists k. apply LevelExprSet.elements_spec1. rewrite e0. now right. }
    clear hcl Heqcall e0.
    generalize (min_atom_value m' e).
    induction l; cbn; auto.
    have -> : min_atom_value m a = min_atom_value m' a.
    { destruct a as [k l'].
      rewrite /min_atom_value. rewrite cl' //.
      exists l'. now left. }
    intros o.
    apply IHl.
    intros x [k l']. apply cl'. exists k. now right.
  Qed.


  Lemma levelmap_find_eq x (m m' : model) :
    (forall k, LevelMap.MapsTo x k m <-> LevelMap.MapsTo x k m') ->
    LevelMap.find x m = LevelMap.find x m'.
  Proof.
   intros hm.
   destruct (LevelMap.find x m) eqn:he;
   destruct (LevelMap.find x m') eqn:he'.
   all:try apply LevelMap.find_2 in he. all:try apply LevelMap.find_2 in he'.
   apply hm in he. eapply LevelMapFact.F.MapsTo_fun in he; tea. congruence.
   apply hm in he. apply LevelMapFact.F.not_find_in_iff in he'. firstorder.
   apply LevelMapFact.F.not_find_in_iff in he. firstorder. congruence.
  Qed.

  Lemma levelmap_find_eq_inv x (m m' : model) :
    LevelMap.find x m = LevelMap.find x m' ->
    (forall k, LevelMap.MapsTo x k m <-> LevelMap.MapsTo x k m').
  Proof.
    intros hfind.
   destruct (LevelMap.find x m) eqn:he;
   destruct (LevelMap.find x m') eqn:he'.
   all:try apply LevelMap.find_2 in he. all:try apply LevelMap.find_2 in he'. all:try congruence.
   noconf hfind. intros k; split; intros.
   eapply LevelMapFact.F.MapsTo_fun in he; tea. now subst.
   eapply LevelMapFact.F.MapsTo_fun in he'; tea. now subst.
   intros k; split; intros.
   apply LevelMapFact.F.not_find_in_iff in he. firstorder.
   apply LevelMapFact.F.not_find_in_iff in he'. firstorder.
  Qed.

  Lemma min_premise_restrict m W (prems : univ) v :
    (forall l k, LevelExprSet.In (l, k) prems -> LevelSet.In l W) ->
    min_premise (restrict_model W m) prems = Some v ->
    min_premise m prems = Some v.
  Proof.
    intros hin.
    rewrite (@min_premise_preserved _ m) //.
    move=> x. rewrite levelexprset_levels_spec => [] [k] /hin inW.
    apply levelmap_find_eq => k'.
    rewrite restrict_model_spec. firstorder.
  Qed.

  Lemma model_of_model_update W m m' :
    model_of W m ->
    model_of W (model_update m m').
  Proof.
    intros hm l hin.
    move/hm: hin => [k hin].
    red. rw model_update_spec.
    destruct (LevelMapFact.F.In_dec m' l).
    - destruct i as [k' hin']. exists k'. right; split => //. now exists k.
    - exists k; left; split => //.
  Qed.

  Lemma strictly_updates_restrict_only_model {cls W m m'} : strictly_updates cls W m m' ->
    only_model_of W (restrict_model W m').
  Proof.
    intros su. red. rw restrict_model_spec.
    split => //. 2:clear; firstorder.
    eapply strictly_updates_total_model in su. move/[dup]/su. clear; firstorder.
  Qed.

  Lemma only_model_of_restrict W m :
    model_of W m -> only_model_of W (restrict_model W m).
  Proof.
    intros mof x. rw restrict_model_spec. firstorder.
  Qed.

  Lemma strictly_updates_from_restrict {cls W W' m m'} :
    clauses_conclusions cls ⊂_lset W ->
    model_of W m ->
    strictly_updates cls W' (restrict_model W m) m' ->
    only_model_of W m'.
  Proof.
    intros hcls mof su.
    have om := strictly_updates_only_model_gen _ _ _ _ su W.
    apply strictly_updates_incl in su.
    have hu : ((W ∪ W') =_lset W). intros x; lsets.
    rewrite hu in om. apply om.
    now apply only_model_of_restrict.
  Qed.

  Lemma restrict_model_update W m m' :
    model_of W m' ->
    only_model_of W m ->
    restrict_model W (model_update m' m) =m m.
  Proof.
    intros mof om.
    intro l. apply levelmap_find_eq => k.
    rewrite restrict_model_spec model_update_spec. split.
    - move=> [] [[hnin hm] hin|hm hin].
     specialize (proj1 (om l) hin) as [x hm']. elim hnin. now exists x.
     apply hm.
    - move=> hm. split => //. 2:now apply om; exists k.
     right; firstorder.
  Qed.

  Lemma model_update_trans m upd upd' :
    (forall l, LevelMap.In l upd -> LevelMap.In l upd') ->
    model_update (model_update m upd) upd' =m model_update m upd'.
  Proof.
    intros hl l. apply levelmap_find_eq => k.
    rewrite !model_update_spec /LevelMap.In.
    rw model_update_spec. firstorder.
    right. split => //.
    destruct (LevelMapFact.F.In_dec upd l).
    - destruct i as [updv hk].
      exists updv. firstorder.
    - exists x; left; firstorder.
  Qed.

  (* If we can update starting from a restricted model with no values outside [W],
     this can be lifted to the unrestricted model, applying the same updates *)
  Lemma strictly_updates_restrict_model_gen cls W W' m' :
    forall cls' mr,
      strictly_updates cls' W' mr m' ->
      forall m, model_of W m ->
      cls' = (cls ⇂ W) ->
      mr =m (restrict_model W m) ->
      strictly_updates (cls ⇂ W) W' m (model_update m m').
  Proof.
    intros cls' mr. induction 1.
    - intros mi mofW -> hm.
      constructor. auto.
      destruct cl as [prems [concl k]].
      destruct H0 as [v [hmin hlt above heq]].
      rewrite hm in hmin, above.
      exists v. split => //.
      eapply min_premise_restrict with W => //.
      { intros l k' hp. move/in_restrict_clauses: H => [] //= _ hsub _. apply hsub.
        rewrite levelexprset_levels_spec. now exists k'. }
      move: above.
      rewrite /level_value_above /level_value.
      elim: find_spec => //.
      + intros kr hkr.
        apply restrict_model_spec in hkr as [hkr hcl].
        now rewrite (LevelMap.find_1 hkr).
      + move=> ncl _.
        elim: find_spec => // => k' inm.
        apply in_restrict_clauses in H as [inconcl inprems incls]. cbn in *.
        elim ncl. exists k'. eapply restrict_model_spec. split => //.
      + apply in_restrict_clauses in H as [inconcl inprems incls]. cbn in *.
        rewrite heq. intro. apply levelmap_find_eq => k'.
        rewrite hm.
        rewrite model_update_spec !LevelMapFact.F.add_mapsto_iff restrict_model_spec.
        rewrite LevelMapFact.F.add_in_iff /Level.eq. firstorder; subst.
        right. split => //. left => //. now apply mofW.
        destruct (inLevelSet W y).
        * right. split. right => //. now exists k'.
        * left. split => //. intros []. congruence.
          destruct H2 as [yrest hin]. eapply restrict_model_spec in hin as []. contradiction.
    - intros mtot mof -> hm. specialize (IHstrictly_updates1 mtot mof eq_refl hm).
      specialize (IHstrictly_updates2 (model_update mtot m')).
      have model_of : model_of W (model_update mtot m').
        by apply model_of_model_update.
      specialize (IHstrictly_updates2 model_of eq_refl).
      forward IHstrictly_updates2.
      { rewrite hm in H. eapply strictly_updates_from_restrict in H; tea.
        2:eapply clauses_conclusions_restrict_clauses.
        now rewrite restrict_model_update. }
      eapply update_trans; tea.
      have eqm : (model_update (model_update mtot m') m'') =m model_update mtot m''.
      { eapply model_update_trans. eapply strictly_updates_ext in H0.
        intros l [k hin]. apply H0 in hin as [k' []]. now exists k'. }
      now rewrite eqm in IHstrictly_updates2.
  Qed.

  Lemma strictly_updates_restrict_model cls W W' m' :
    forall m, model_of W m ->
    strictly_updates (cls ⇂ W) W' (restrict_model W m) m' ->
    strictly_updates (cls ⇂ W) W' m (model_update m m').
  Proof.
    intros m mof su.
    eapply strictly_updates_restrict_model_gen; tea; reflexivity.
  Qed.

  Lemma strictly_updates_is_update_of_restrict cls W init m W' m' :
    strictly_updates cls W init m ->
    is_update_of (cls ⇂ W) W' (restrict_model W m) m' ->
    strictly_updates cls (LevelSet.union W W') init (model_update m m').
  Proof.
    move=> su /is_update_of_case; intros [[empw eq]|su'].
    - rewrite <- eq. eapply (strictly_updates_weaken cls). clsets.
      rewrite model_update_restrict.
      eapply strictly_updates_W_eq; tea. lsets.
    - eapply strictly_updates_restrict_model in su'.
      eapply strictly_updates_weaken in su'. 2:eapply restrict_clauses_subset.
      eapply update_trans; tea; eapply strictly_updates_weaken; tea; clsets.
      now apply strictly_updates_total_model in su.
  Qed.

  Lemma union_with_concl cls W : Clauses.Equal (Clauses.union cls (cls ↓ W)) cls.
  Proof.
    intros x. rewrite Clauses.union_spec in_clauses_with_concl. firstorder.
  Qed.

  Instance is_update_of_proper : Proper (Clauses.Equal ==> LevelSet.Equal ==> LevelMap.Equal ==> LevelMap.Equal ==> iff) is_update_of.
  Proof.
    intros ?? H ?? H' ?? H'' ?? H'''.
    unfold is_update_of. setoid_rewrite H'. destruct LevelSet.is_empty.
    rewrite H'' H'''. reflexivity.
    firstorder. now rewrite -H -H' -H'' -H'''.
    subst. now rewrite H H' H'' H'''.
  Qed.

  Lemma empty_union l : LevelSet.Equal (LevelSet.union LevelSet.empty l) l.
  Proof. intros ?. lsets. Qed.

  Lemma is_update_of_strictly_updates cls W m m' :
    strictly_updates cls W m m' ->
    is_update_of cls W m m'.
  Proof.
    intros su. have ne := strictly_updates_non_empty su.
    rewrite /is_update_of. now rewrite (proj2 (levelset_not_Empty_is_empty _) ne).
  Qed.

  Lemma is_update_of_weaken {cls cls' W m m'} :
    Clauses.Subset cls cls' ->
    is_update_of cls W m m' -> is_update_of cls' W m m'.
  Proof.
    intros hsub.
    move/is_update_of_case => [].
    - intros []. subst. rewrite /is_update_of.
      now rewrite (LevelSetFact.is_empty_1 H).
    - intros su. have ne := strictly_updates_non_empty su.
      unfold is_update_of. rewrite (proj2 (levelset_not_Empty_is_empty _) ne).
      eapply strictly_updates_weaken; tea.
  Qed.

  Lemma is_update_of_trans {cls cls' W W' m m' m''} :
    is_update_of cls W m m' -> is_update_of cls' W' m' m'' ->
    is_update_of (Clauses.union cls cls') (LevelSet.union W W') m m''.
  Proof.
    move/is_update_of_case => [].
    - move=> [he eq]. intro. rewrite eq. rewrite (LevelSetProp.empty_is_empty_1 he) empty_union.
      move: H. eapply is_update_of_weaken. clsets.
    - intros su isu.
      eapply strictly_updates_is_update_of in isu; tea.
      have ne := strictly_updates_non_empty isu.
      rewrite /is_update_of. now rewrite (proj2 (levelset_not_Empty_is_empty _) ne).
  Qed.

  Lemma is_update_of_trans_eq {cls cls' W W' cltr Wtr m m' m''} :
    is_update_of cls W m m' -> is_update_of cls' W' m' m'' ->
    Clauses.Subset (Clauses.union cls cls') cltr ->
    LevelSet.Equal Wtr (LevelSet.union W W') ->
    is_update_of cltr Wtr m m''.
  Proof.
    intros hi hi' hcl hw. rewrite hw.
    eapply is_update_of_weaken; tea.
    eapply is_update_of_trans; tea.
  Qed.

  Lemma union_idem cls : Clauses.Equal (Clauses.union cls cls) cls.
  Proof. intros ?; rewrite Clauses.union_spec. firstorder. Qed.

  Lemma above_max_premise_model_trans {cls V' m m'} :
    above_max_premise_model cls m ->
    strictly_updates cls V' m m' ->
    above_max_premise_model cls m'.
  Proof.
    move=> [[V'' ab]|eq] su.
    * have tr := strictly_updates_trans ab su.
      rewrite union_idem in tr.
      now left; eexists.
    * left; exists V'. now subst.
  Qed.

  Lemma max_clause_premise_spec2 cls :
    (exists cl, Clauses.In cl cls /\ max_clause_premise cls = premise_max (premise cl)) \/
    (Clauses.Empty cls /\ max_clause_premise cls = 0%nat).
  Proof.
    unfold max_clause_premise.
    eapply ClausesProp.fold_rec.
    - firstorder.
    - intros x a s' s'' incls ins' hadd [ih|ih].
      left.
      * destruct ih as [cl [incl ->]].
        destruct (Nat.max_spec (premise_max (premise x)) (premise_max (premise cl))) as [[hlt ->]|[hge ->]].
        { exists cl. split => //. apply hadd. now right. }
        { exists x. firstorder. }
      * left. exists x. split; firstorder. subst.
        lia.
  Qed.

  Lemma max_clause_premise_mon {cls cls'} :
    cls ⊂_clset cls' ->
    (max_clause_premise cls <= max_clause_premise cls')%nat.
  Proof using Type.
    intros hincl.
    have [[cl [hin hs]]|[he hs]] := max_clause_premise_spec2 cls;
    have [[cl' [hin' hs']]|[he' hs']] := max_clause_premise_spec2 cls'.
    - apply hincl in hin.
      have hm := max_clause_premise_spec _ _ hin.
      have hm' := max_clause_premise_spec _ _ hin'. lia.
    - rewrite hs'. apply hincl in hin. now eapply he' in hin.
    - rewrite hs. lia.
    - lia.
  Qed.


  Lemma update_total_model W m m' :
     model_of W m ->
     model_of W (model_update m m').
  Proof.
    intros mof k inW.
    apply mof in inW as [v inW].
    destruct (LevelMapFact.F.In_dec m' k).
    - destruct i as [v' inm']. exists v'.
      rewrite model_update_spec. right; firstorder.
    - exists v. rewrite model_update_spec. left. split => //.
  Qed.

  Lemma model_map_outside_update W m m' :
    only_model_of W m' ->
    model_map_outside W m (model_update m m').
  Proof.
    intros om l nin k.
    rewrite model_update_spec.
    firstorder.
  Qed.

  Lemma valid_model_only_model W W' m cls :
    forall vm : valid_model W W' m cls,
    only_model_of W m -> only_model_of W (model_model vm).
  Proof.
    intros vm.
    have incl := model_incl vm.
    destruct vm as [m' mof isupd clsincl ism]. cbn.
    move: isupd; rewrite /is_update_of.
    destruct LevelSet.is_empty eqn:heq. now intros ->.
    intros su om.
    eapply strictly_updates_only_model_gen in su; tea.
    eapply only_model_of_eq; tea. intro. lsets.
  Qed.

  Lemma valid_model_is_update_of W W' m cls :
    model_of W m ->
    forall vm : valid_model W W' (restrict_model W m) (cls ⇂ W),
    is_update_of (cls ⇂ W) W' m (model_update m (model_model vm)).
  Proof.
    intros mofW vm.
    have incl := model_incl vm.
    destruct vm as [m' mof isupd clsincl ism]. cbn.
    move: isupd. rewrite /is_update_of.
    destruct LevelSet.is_empty eqn:he.
    - intros <-. now rewrite model_update_restrict.
    - intros su. eapply strictly_updates_restrict_model in su; tea.
  Qed.

  Infix "=_clset" := Clauses.Equal (at level 90).

  Lemma valid_model_is_update_of_eq W W' m cls cls' :
    model_of W m ->
    forall vm : valid_model W W' (restrict_model W m) cls,
    cls =_clset (cls' ⇂ W) ->
    is_update_of cls W' m (model_update m (model_model vm)).
  Proof.
    intros mofW vm.
    have incl := model_incl vm.
    destruct vm as [m' mof isupd clsincl ism]. cbn.
    move: isupd. rewrite /is_update_of.
    destruct LevelSet.is_empty eqn:he.
    - intros <-. now rewrite model_update_restrict.
    - intros su eq. rewrite eq in su. eapply strictly_updates_restrict_model in su; tea.
      now rewrite eq.
  Qed.

  Lemma valid_clause_preserved {m m' cl} :
    (forall x, LevelSet.In x (clause_levels cl) -> level_value m x = level_value m' x) ->
    valid_clause m cl ->
    valid_clause m' cl.
  Proof.
    intros hcl. destruct cl as [prems [concl k]].
    rewrite /valid_clause //=.
    rewrite (@min_premise_preserved m m' prems).
    { intros x inp. apply hcl. rewrite clause_levels_spec. now left. }
    destruct (min_premise m' prems) => //.
    rewrite /level_value_above. rewrite hcl //.
    rewrite clause_levels_spec. now right.
  Qed.

  Lemma is_model_update W m m' cls :
    model_of W m ->
    only_model_of W m' ->
    is_model (cls ⇂ W) m' ->
    is_model (cls ⇂ W) (model_update m m').
  Proof.
    intros mW om.
    rewrite /is_model.
    move/Clauses.for_all_spec. intros h.
    apply Clauses.for_all_spec. tc.
    intros cl hin.
    specialize (h cl hin). cbn in h.
    eapply valid_clause_preserved; tea.
    move=>x; move: hin. rewrite in_restrict_clauses.
    intros [incl inprems incls].
    rewrite clause_levels_spec. move=> [] hin.
    - apply inprems in hin.
      rewrite /level_value.
      apply levelmap_find_eq => k.
      rewrite model_update_spec. clear -mW om hin. firstorder.
    - subst x. apply levelmap_find_eq => k.
      rewrite model_update_spec. cbn in *. firstorder. cbn in H.
      apply om in incl as [x hm]. now apply H in hm.
  Qed.

  Context (V : LevelSet.t) (U : LevelSet.t) (init_model : model)
    (loop : forall (V' U' : LevelSet.t) (cls' : clauses) (minit m : model)
    (prf : [/\ clauses_levels cls' ⊂_lset V', only_model_of V' minit &
      is_update_of cls' U' minit m]),
    lexprod_rel (loop_measure V' U') (loop_measure V U) -> result V' U' cls' minit).

  Section innerloop_partition.
    Context (W : LevelSet.t) (cls : clauses).
    Context (premconclW conclW : clauses).
    Context (prf : [/\ strict_subset W V, ~ LevelSet.Empty W, U ⊂_lset W, clauses_conclusions cls ⊂_lset W,
      Clauses.Equal premconclW (cls ⇂ W) & Clauses.Equal conclW (Clauses.diff (cls ↓ W) (cls ⇂ W))]).

    #[tactic="idtac"]
    Equations? inner_loop_partition (m : model) (upd : strictly_updates cls W init_model m) :
      result W LevelSet.empty cls m
      by wf (measure W cls m) lt :=
      inner_loop_partition m upd with loop W LevelSet.empty premconclW (restrict_model W m) (restrict_model W m) _ _ := {
        (* premconclW = cls ⇂ W , conclW = (Clauses.diff (cls ↓ W) (cls ⇂ W)) *)
        | Loop u isl => Loop u (loop_on_subset _ isl)
        (* We have a model for (cls ⇂ W), we try to extend it to a model of (csl ↓ W).
          By invariant Wr ⊂ W *)
        | Model Wr mr empWr with inspect (check_model conclW (Wr, model_update m (model_model mr))) := {
          | exist None eqm => Model Wr {| model_model := model_update m (model_model mr) |} _
          | exist (Some (Wconcl, mconcl)) eqm with inner_loop_partition mconcl _ := {
            (* Here Wr ⊂ Wconcl by invariant *)
              | Loop u isl => Loop u isl
              | Model Wr' mr' UWconcl => Model (LevelSet.union Wconcl Wr') {| model_model := model_model mr' |} _ }
              (* Here Wr' ⊂ W by invariant *)
        (* We check if the new model [mr] for (cls ⇂ W) extends to a model of (cls ↓ W). *)
        (* We're entitled to recursively compute a better model starting with mconcl,
          as we have made the measure decrease:
          some atom in W has been strictly updated in Wconcl. *)
            } }.
    Proof.
      all:try solve [try apply LevelSet.subset_spec; try reflexivity].
      all:cbn [model_model]; clear loop inner_loop_partition.
      all:try apply LevelSet.subset_spec in hsub.
      all:auto.
      all:try destruct prf as [WV neW UW clsW eqprem eqconcl].
      all:try solve [intuition auto].
      all:try rewrite eqconcl in eqm.
      - split => //.
        * rewrite eqprem. apply clauses_levels_restrict_clauses.
        * now eapply strictly_updates_restrict_only_model.
        (* * eapply (strictly_updates_total_model upd). *)
        (* * rewrite eqprem. transitivity cls => //. apply restrict_clauses_subset. *)
        (* * eapply strictly_updates_weaken in upd; tea. eapply above_max_premise_model_trans in maxp; tea. *)
        * eapply is_update_of_empty.
      - left. now eapply strict_subset_cardinal.
      - rewrite eqprem. eapply restrict_clauses_subset.
      (* - destruct prf. transitivity (cls ⇂ W) => //. now rewrite H3. eapply restrict_clauses_subset. *)
      - have mu := model_updates mr.
        setoid_rewrite eqprem at 1 in mu.
        eapply strictly_updates_is_update_of_restrict in upd; tea.
        apply check_model_spec in eqm as [Wconcl' [sumr ->]].
        have tr := strictly_updates_trans upd sumr.
        eapply strictly_updates_clauses_W; tea.
        { intros ?. now rewrite ClausesProp.union_sym union_diff_cls. }
        { have incl := model_incl mr. apply strictly_updates_incl in sumr.
          have hdiff := clauses_conclusions_diff_left cls W (cls ⇂ W). lsets. }
      - have tmr : model_of W (model_model mr).
        { eapply valid_model_total. eapply strictly_updates_restrict_only_model in upd.
          intro. apply upd. }
        have tmr' : model_of W (model_update m (model_model mr)).
        { eapply update_total_model; tea. now apply strictly_updates_total_model in upd. }
        eapply (check_model_spec_diff tmr') in eqm as [subwwconcl subwconcl hm hext] => //.
        pose proof (clauses_conclusions_diff_left cls W (cls ⇂ W)).
        destruct hm as [cll [hind nvalid inwconcl hl]].
        eapply Nat.lt_le_trans with (measure W cls (model_update m (model_model mr))).
        2:{ eapply measure_le; eauto; try eapply mr; tea.
            - now eapply strictly_updates_total_model in upd.
            - apply model_map_outside_update. eapply valid_model_only_model.
              now eapply strictly_updates_restrict_only_model.
            - eapply is_update_of_ext.
              have mof := strictly_updates_model_of upd.
              apply: valid_model_is_update_of_eq _ _ _ _ cls mof mr eqprem. }
        eapply measure_lt; tea.
        { eapply model_map_outside_weaken. eapply hext. have incl := model_incl mr. lsets. }
        { apply hext. }
        eapply invalid_clause_measure in nvalid; tea.
        exists (levelexpr_level (concl cll)).
        split => //.
        eapply clauses_conclusions_diff_left; tea.
        eapply clauses_conclusions_spec. exists cll; split => //. exact hind.
        have incl := model_incl mr. eapply model_of_subset; tea.
      - apply mr'.
      - have updm : is_update_of premconclW Wr m (model_update m (model_model mr)).
        { exact: valid_model_is_update_of_eq _ _ _ _ cls (strictly_updates_model_of upd) mr eqprem. }
        eapply check_model_is_update_of in eqm as [eqm incl]. 2:eapply updm.
        eapply strictly_updates_is_update_of in eqm. 2:eapply mr'.
        eapply is_update_of_strictly_updates in eqm.
        eapply is_update_of_weaken; tea.
        now rewrite eqprem (ClausesProp.union_sym (cls ⇂ W)) union_diff ClausesProp.union_sym union_with_concl.
      - apply mr'.
      - lsets.
      - have updm : is_update_of premconclW Wr m (model_update m (model_model mr)).
        { exact: valid_model_is_update_of_eq _ _ _ _ cls (strictly_updates_model_of upd) mr eqprem. }
        eapply update_total_model. now apply strictly_updates_model_of in upd.
      - have updm : is_update_of premconclW Wr m (model_update m (model_model mr)).
        { exact: valid_model_is_update_of_eq _ _ _ _ cls (strictly_updates_model_of upd) mr eqprem. }
        eapply is_update_of_weaken. 2:apply updm. rewrite eqprem. apply restrict_clauses_subset.
      - rewrite check_model_is_model in eqm.
        have okm := (model_ok mr).
        have okupdm : is_model premconclW (model_update m (model_model mr)).
        { setoid_rewrite eqprem at 1. apply is_model_update. apply strictly_updates_model_of in upd; tea.
           eapply valid_model_only_model. now eapply strictly_updates_restrict_only_model.
           now setoid_rewrite <- eqprem at 1. }
        have mu := is_model_union okupdm eqm.
        rewrite {1}eqprem in mu.
        rewrite union_diff_eq in mu.
        rewrite union_restrict_with_concl in mu.
        now rewrite (clauses_conclusions_eq _ _ clsW).
    Qed.
  End innerloop_partition.

  (* We first partition the clauses among those that mention only W and the ones that can mention other atoms.
     We then call the loop on these two sets of clauses, which not need to change during the recursive calls.
    *)
  #[tactic="idtac"]
  Equations? inner_loop (W : LevelSet.t) (cls : clauses) (m : model)
    (prf : [/\ strict_subset W V, ~ LevelSet.Empty W, U ⊂_lset W, clauses_conclusions cls ⊂_lset W &
      strictly_updates cls W init_model m]) : result W LevelSet.empty cls m :=
    inner_loop W cls m prf with inspect (Clauses.partition (premise_restricted_to W) cls) :=
      | exist (premconclW, conclW) eqp => inner_loop_partition W cls premconclW conclW _ m _.
  Proof.
    - destruct prf as [subWV neW UW clsW mW].
      eapply (clauses_partition_spec clsW) in eqp as [eqprem eqconcl].
      split => //. now rewrite -(clauses_conclusions_eq _ _ clsW).
    - apply prf.
  Qed.

End InnerLoop.

Local Open Scope nat_scope.
Lemma diff_cardinal_inter V W : #|LevelSet.diff V W| = #|V| - #|LevelSet.inter V W|.
Proof.
  pose proof (LevelSetProp.diff_inter_cardinal V W). lia.
Qed.

Lemma diff_cardinal V W : W ⊂_lset V -> #|LevelSet.diff V W| = #|V| - #|W|.
Proof.
  intros hsub.
  rewrite diff_cardinal_inter LevelSetProp.inter_sym LevelSetProp.inter_subset_equal //.
Qed.

Lemma is_modelP m cls : reflect (Clauses.For_all (valid_clause m) cls) (is_model cls m).
Proof.
  case E: is_model; constructor.
  - now move: E; rewrite /is_model -ClausesFact.for_all_iff.
  - intros hf. apply ClausesFact.for_all_iff in hf; tc. unfold is_model in E; congruence.
Qed.

Lemma is_model_invalid_clause cl cls m : is_model cls m -> ~~ valid_clause m cl -> ~ Clauses.In cl cls.
Proof.
  move/is_modelP => ism /negP valid hin.
  now specialize (ism _ hin).
Qed.

Lemma strict_subset_leq_right U V W :
  strict_subset U V -> V ⊂_lset W -> strict_subset U W.
Proof.
  intros [] le. split. lsets. intros eq. rewrite -eq in le.
  apply H0. lsets.
Qed.

Lemma strict_subset_leq_left U V W :
  U ⊂_lset V -> strict_subset V W -> strict_subset U W.
Proof.
  intros le []. split. lsets. intros eq. rewrite eq in le.
  apply H0. lsets.
Qed.

(* Lemma strict_subset_union_right U U' V W :
  strict_subset V W -> U ⊂_lset U' ->
  strict_subset (LevelSet.union U V) (LevelSet.union U' W).
Proof.
  rewrite /strict_subset.
  intros [] hu. split. lsets. intros he.
  apply H0.
  intros x. split. apply H.
  specialize (he x). intros inW.
  rewrite !LevelSet.union_spec in he.
  destruct he as [he he'].
  forward he'. now right. destruct he' => //.
  forward he. apply he in
  red in he. *)

Lemma strict_subset_diff_incl V W W' :
  strict_subset W' W ->
  W ⊂_lset V ->
  W' ⊂_lset V ->
  strict_subset (LevelSet.diff V W) (LevelSet.diff V W').
Proof.
  intros [] lew lew'.
  split. lsets.
  intros eq.
  apply H0. lsets.
Qed.

(* To help equations *)
Opaque lexprod_rel_wf.

Lemma check_model_spec_V {V cls w m w' m'} :
  model_of V m -> clauses_conclusions cls ⊂_lset V ->
  model_of w m ->
  check_model cls (w, m) = Some (w', m') ->
  check_model_invariants cls w m w' m' true.
Proof.
  cbn; intros mof incl tot cm.
  apply check_model_has_invariants in cm => //.
  eapply model_of_subset. exact mof. tea.
Qed.

Section Semantics.

  Section Interpretation.
    Context (V : LevelMap.t nat).

    Definition interp_level l :=
      match LevelMap.find l V with
      | Some x => x
      | None => 0%nat
      end.

    Definition interp_expr '(l, k) := (interp_level l + k)%nat.
    Definition interp_prems prems :=
      let '(hd, tl) := to_nonempty_list prems in
      fold_right (fun lk acc => Nat.max (interp_expr lk) acc) (interp_expr hd) tl.

    Definition clause_sem (cl : clause) : Prop :=
      let '(prems, concl) := cl in
      interp_prems prems >= interp_expr concl.

    Definition clauses_sem (cls : clauses) : Prop :=
      Clauses.For_all clause_sem cls.
  End Interpretation.

  (* There exists a valuation making all clauses true in the natural numbers *)
  Definition satisfiable (cls : clauses) :=
    exists V, clauses_sem V cls.

  (* Any valuation making all clauses valid in the natural numbers also satisfies the clause cl *)
  Definition entails_sem (cls : clauses) (cl : clause) :=
    forall V, clauses_sem V cls -> clause_sem V cl.
End Semantics.


Local Open Scope Z_scope.
Lemma max_min max min k : min <= 0 -> max >= 0 -> k <= max -> k >= min -> (max - k - min) >= 0.
Proof. lia. Qed.

Definition model_min m :=
  LevelMap.fold (fun l k acc => Nat.min acc k) m 0%nat.

(* Lemma model_min_spec m : forall l k, LevelMap.MapsTo l k m -> (Some (model_min m) ≤ k). *)
(* Proof. Admitted. *)

Definition model_max m :=
  LevelMap.fold (fun l k acc => Nat.max acc k) m 0%nat.

Lemma model_max_spec m : forall l k, LevelMap.MapsTo l k m -> (k <= model_max m)%nat.
Proof. Admitted.

Definition valuation_of_model (m : model) : LevelMap.t nat :=
  let max := model_max m in
  LevelMap.fold (fun l k acc => LevelMap.add l (max - k)%nat acc) m (LevelMap.empty _).
Close Scope Z_scope.

Lemma valuation_of_model_spec m :
  forall l k, LevelMap.MapsTo l k m ->
    let v := (model_max m - k )%nat in
    LevelMap.MapsTo l v (valuation_of_model m).
Proof. Admitted.

Lemma strictly_updates_valid_model {W W' m m' cls} :
  is_model (cls ↓ W) m ->
  strictly_updates cls W' m m' ->
  exists l, LevelSet.In l W' /\ ~ LevelSet.In l W.
Proof.
  intros vm. induction 1.
  - exists (clause_conclusion cl). split => //. lsets. intros hin.
    eapply strict_update_invalid in H0.
    eapply is_model_invalid_clause in vm; tea. apply vm.
    eapply in_clauses_with_concl. split => //.
  - destruct (IHstrictly_updates1 vm). exists x.
    rewrite LevelSet.union_spec. firstorder.
Qed.

Lemma model_of_strictly_updates cls W V m m' :
  strictly_updates cls W m m' -> model_of V m -> model_of V m'.
Proof.
  intros su.
  induction su.
  - intros mv l hin. apply mv in hin.
    destruct cl as [prems [concl k]].
    destruct H0 as [minv [eqmin hlt nabove eqm]]. rewrite eqm.
    rewrite LevelMapFact.F.add_in_iff. now right.
  - eauto.
Qed.

Lemma check_model_ne {cls U m W m'} : check_model cls (U, m) = Some (W, m') -> ~ LevelSet.Empty W.
Proof.
  move/check_model_spec => [w'' [su ->]].
  apply strictly_updates_non_empty in su.
  intros he. apply su. lsets.
Qed.

Lemma check_model_update_of {cls U m W m'} : check_model cls (U, m) = Some (W, m') ->
  exists W', is_update_of cls W' m m' /\ W = LevelSet.union U W'.
Proof.
  move/check_model_spec => [w'' [su ->]]. exists w''. split => //.
  now eapply is_update_of_strictly_updates.
Qed.

Axiom todo : forall {A}, A.

Lemma opt_le_lt_trans {x y z} : opt_le Z.le x y -> opt_le Z.lt y z -> opt_le Z.lt x z.
Proof.
  destruct 1; intros H'; depelim H'; constructor. lia.
Qed.

Lemma strictly_updates_all cls V minit m : strictly_updates cls V minit m ->
  (forall l k, LevelSet.In l V -> LevelMap.MapsTo l k minit -> exists k', LevelMap.MapsTo l k' m /\ Nat.lt k k').
Proof.
  induction 1.
  - intros l k hin hm.
    move: H0; rewrite /strict_update.
    destruct cl as [prems [concl gain]].
    move=> [] v [] minp hlt. cbn in hin. eapply LevelSet.singleton_spec in hin. red in hin; subst l.
    move/negbTE; rewrite /level_value_above.
    intros hle eq. setoid_rewrite eq.
    eexists. setoid_rewrite LevelMapFact.F.add_mapsto_iff. split; [left;split;eauto|] => //.
    destruct level_value eqn:hl => //.
    * rewrite (level_value_MapsTo hm) in hl. noconf hl. lia.
    * rewrite (level_value_MapsTo hm) in hl. noconf hl.
  - intros l k; rewrite LevelSet.union_spec; move=> [] hin hm.
    apply IHstrictly_updates1 in hm as [k' [hle hm']]; tea.
    eapply strictly_updates_ext in H0. apply H0 in hle as [k'' [hm'' lek'']].
    exists k''. split => //. lia.
    eapply strictly_updates_ext in H. eapply H in hm as [k' [hm' lek']].
    eapply IHstrictly_updates2 in hm' as [k'' [hm'' lek'']]; tea.
    exists k''. split => //. lia.
Qed.

Lemma strictly_updates_zero_model cls V mzero m :
  (forall l, LevelSet.In l V -> LevelMap.MapsTo l 0%nat mzero) ->
  strictly_updates cls V mzero m ->
  forall l, LevelSet.In l V -> exists k, LevelMap.MapsTo l k m /\ (0 < k).
Proof.
  intros ho.
  move/strictly_updates_all => ha l hin.
  eapply ha in hin; revgoals. now apply ho.
  destruct hin as [k' [hm hle]].
  now exists k'.
Qed.

Lemma of_level_set_union_spec {ls ls' n hne} hne' hne'' :
  of_level_set (ls ∪ ls') n hne =
  univ_union (of_level_set ls n hne') (of_level_set ls' n hne'').
Proof.
  apply eq_univ'.
  intros [l k]. rewrite /of_level_set //= !levelexprset_of_levels_spec LevelExprSet.union_spec.
  rewrite !levelexprset_of_levels_spec LevelSet.union_spec. clear. firstorder.
Qed.

Lemma in_singleton l : LevelSet.In l (LevelSet.singleton l).
Proof. lsets. Qed.

Definition app {A B} (f : A -> B) (x : A) := f x.

Notation "f $ x" := (app f x) (at level 20).

Definition model_domain (m : model) V :=
  forall x, LevelSet.In x V <-> LevelMap.In x m.

Definition model_rel_partial R V (m m' : model) :=
  forall l,
    (LevelSet.In l V -> forall k, LevelMap.MapsTo l k m ->
       exists k', LevelMap.MapsTo l k' m' /\ R k k') /\
    (~ LevelSet.In l V -> forall k, LevelMap.MapsTo l k m <-> LevelMap.MapsTo l k m').

Lemma model_of_sext {R W W' m m'} :
  model_of W m ->
  model_of W' m ->
  model_rel_partial R W m m' -> model_of W' m'.
Proof.
  intros mof mof' ext.
  intros l hin.
  destruct (mof' l hin). specialize (ext l) as [lin lout].
  destruct (inLevelSet W l) as [hin'|hout].
  - specialize (lin hin' _ H). firstorder.
  - specialize (lout hout x).
    exists x. now apply lout.
Qed.

Lemma not_in_union_inv l ls ls' :
  ~ LevelSet.In l (LevelSet.union ls ls') ->
  ~ LevelSet.In l ls /\ ~ LevelSet.In l ls'.
Proof.
  rewrite LevelSet.union_spec. firstorder.
Qed.

Lemma model_rel_partial_trans {R W W' m m' m''} (HR : Transitive R) :
  model_rel_partial R W m m' ->
  model_rel_partial R W' m' m'' ->
  model_rel_partial R (LevelSet.union W W') m m''.
Proof.
  intros mr mr' l.
  specialize (mr l) as [inWmr outWmr].
  specialize (mr' l) as [inWmr' outWmr'].
  split.
  { rewrite LevelSet.union_spec. move=> [] hin k hm.
    - specialize (inWmr hin k hm) as [k' [hk' rk']].
      destruct (inLevelSet W' l).
      + specialize (inWmr' H k' hk') as [k'' [hk'' rk'']].
        exists k''. split => //. now transitivity k'.
      + specialize (outWmr' H k'). exists k'. split => //. now apply outWmr'.
    - destruct (inLevelSet W l).
      + specialize (inWmr H k hm) as [k'' [hk'' rk'']].
        specialize (inWmr' hin k'' hk'') as [km' [hkm' rkm']].
        exists km'. split => //. now transitivity k''.
      + specialize (outWmr H k) as eq.
        apply eq in hm.
        specialize (inWmr' hin k hm) as [m''k [hm'' rm'']].
        exists m''k. split => //. }
  { move/not_in_union_inv => [] ninW ninW' k.
    rewrite (outWmr ninW k).
    rewrite (outWmr' ninW' k). reflexivity. }
Qed.

Lemma strictly_updates_model_lt {cls V} {m m'} :
  strictly_updates cls V m m' ->
  model_of V m ->
  model_rel_partial Nat.lt V m m'.
Proof.
  intros su; induction su.
  - intros htot l. split; revgoals.
    { intros nin k. destruct cl as [prems [concl conclk]]; cbn in *.
      destruct H0 as [minp [hmin hlt nabove hm']].
      rewrite hm'. rewrite LevelMapFact.F.add_mapsto_iff.
      assert (concl <> l). intros ->.
      apply nin, in_singleton.
      firstorder. }
    intros inv k hin.
    red in htot.
    specialize (htot (clause_conclusion cl) (in_singleton _)) as [mconcl mt].
    destruct cl as [prems [concl conclk]]; cbn in *.
    destruct H0 as [minp [hmin hlt nabove hm']].
    eapply LevelSet.singleton_spec in inv; red in inv; subst l.
    eapply LevelMapFact.F.MapsTo_fun in hin; tea. noconf hin.
    exists (conclk + Z.to_nat minp)%nat. split => //.
    rewrite hm'.
    rewrite LevelMapFact.F.add_mapsto_iff. left. split => //.
    move/negbTE: nabove; move/level_value_not_above_spec.
    rewrite (level_value_MapsTo mt). now intros x; depelim x.
  - move/model_of_union_inv => [] totls totls'.
    forward IHsu1 by auto.
    forward IHsu2.
    { eapply model_of_sext. exact totls. assumption. eassumption. }
    now eapply model_rel_partial_trans.
Qed.

Lemma intro_sing {P : Level.t -> Prop} {cl} :
  P cl -> (forall l, LevelSet.In l (LevelSet.singleton cl) -> P l).
Proof.
  intros H l ins. rewrite LevelSet.singleton_spec in ins. now red in ins; subst.
Qed.

Lemma elim_sing {P : Level.t -> Prop} {cl} : (forall l, LevelSet.In l (LevelSet.singleton cl) -> P l) -> P cl.
Proof.
  intros H. apply H, in_singleton.
Qed.

#[program]
Definition of_level_map (m : LevelMap.t nat) (hne : ~ LevelMap.Empty m) : nonEmptyLevelExprSet :=
  {| t_set := LevelMap.fold (fun l k acc => LevelExprSet.add (l, k) acc) m LevelExprSet.empty |}.
Next Obligation. apply not_Empty_is_empty.
  move: hne. eapply LevelMapFact.fold_rec. firstorder.
  intros. rewrite /LevelExprSet.Empty.
  rw LevelExprSet.add_spec. intros ha. apply (ha (k, e)). now left.
Qed.

Lemma of_level_map_spec m hne :
  forall l k, LevelExprSet.In (l, k) (of_level_map m hne) <-> LevelMap.MapsTo l k m.
Proof.
  intros l k; rewrite /of_level_map //=.
  clear hne.
  have : forall acc,
    LevelExprSet.In (l, k)
    (LevelMap.fold (fun (l0 : LevelMap.key) (k0 : nat) (acc : LevelExprSet.t) => LevelExprSet.add (l0, k0) acc) m acc) <->
    LevelMap.MapsTo l k m \/ LevelExprSet.In (l, k) acc.
  move=> acc; eapply LevelMapFact.fold_rec.
  - firstorder.
  - intros. rewrite LevelExprSet.add_spec H2.
    split.
    * intros [eq|hm].
      + noconf eq. specialize (H1 l). eapply levelmap_find_eq_inv in H1.
        erewrite H1. left. apply LevelMapFact.F.add_mapsto_iff. left => //.
      + specialize (H1 l). eapply levelmap_find_eq_inv in H1; erewrite H1.
        rewrite LevelMapFact.F.add_mapsto_iff.
        destruct (eq_dec l k0); subst; firstorder.
    * intros hm'. destruct hm'.
      + specialize (H1 l). eapply levelmap_find_eq_inv in H1. eapply H1 in H3.
        apply LevelMapFact.F.add_mapsto_iff in H3. destruct H3. firstorder; subst. left. red. red in H3. subst. reflexivity.
        unfold LevelExprSet.E.eq. destruct H3. now right; left.
      + unfold LevelExprSet.E.eq. now right.
  - intros. rewrite H. firstorder. lesets.
Qed.

Definition premise_values (prems : univ) m :=
  NonEmptySetFacts.map (fun '(l, k) => (l, option_get 0 (level_value m l))) prems.

Lemma premise_values_spec prems m :
  forall l k, LevelExprSet.In (l, k) (premise_values prems m) <->
    (exists k', LevelExprSet.In (l, k') prems /\ k = option_get 0 (level_value m l)).
Proof.
  rewrite /premise_values.
  intros l k. rewrite NonEmptySetFacts.map_spec.
  firstorder. destruct x. noconf H0.
  exists n. split => //.
Qed.

Definition hyps_map (hyps : univ) m :=
  (forall (l : Level.t) (k : nat), LevelExprSet.In (l, k) hyps <-> LevelMap.MapsTo l k m).

Lemma model_hyps_entails cls m hyps (prems : univ) concl :
  Clauses.In (prems, concl) cls ->
  (forall l k, LevelExprSet.In (l,k) prems -> Some 0 ≤ level_value m l) ->
  hyps_map hyps m ->
  cls ⊢a hyps → premise_values prems m.
Proof.
  intros incls hmx hm.
  intros [l k] hin.
  rewrite premise_values_spec in hin. destruct hin as [k' [inp ->]].
  red in hm.
  constructor. rewrite hm.
  specialize (hmx l _ inp).
  depelim hmx. rewrite H0 //=.
  now eapply level_value_MapsTo'.
Qed.

Lemma entails_succ cls (u v : univ) :
  (forall l k, LevelExprSet.In (l, k) v -> exists k', LevelExprSet.In (l, k') u /\ k <= k') ->
  cls ⊢a u → v.
Proof.
  intros hk [l k] hin.
  specialize (hk _ _ hin) as [k' [hin' le]].
  assert (exists n, k' = k + n) as [n ->] by (exists (k' - k); lia).
  eapply (entails_pred_closure_n (n := n)).
  now constructor.
Qed.

Lemma hyps_entails (hyps : univ) m cls :
  hyps_map hyps m ->
  forall prems conclk, Clauses.In (prems, conclk) cls ->
  forall v, min_premise m prems = Some (Z.of_nat v) ->
  cls ⊢a hyps → add_prems v prems.
Proof.
  intros H prems conclk H0 v H1.
  have [minsleq mineq] := min_premise_spec m prems.
  destruct mineq as [[minprem minpremk] [inprems eqminp]]. cbn.
  have hmz' : forall l k, LevelExprSet.In (l, k) prems -> Some 0 ≤ level_value m l.
  { intros l k hin. specialize (minsleq _ hin). rewrite H1 in minsleq. cbn in minsleq. destruct level_value => //.
    depelim minsleq. constructor. lia. depelim minsleq. }
  move: eqminp. rewrite /min_atom_value.
  destruct level_value eqn:hl. intros hminp.
  2:{ now rewrite H1. }
  rewrite H1 in hminp. noconf hminp.
  have entails_prems : cls ⊢a hyps → premise_values prems m.
    by eapply model_hyps_entails with conclk; auto.
  eapply entails_all_trans; tea.
  eapply entails_succ.
  intros l k. rewrite In_add_prems.
  intros [[prem premk] [inprem [= -> ->]]].
  rw premise_values_spec. eexists.
  split. exists premk. split => //.
  have hmz'' := hmz' prem _ inprem.
  depelim hmz''. rewrite H4 //=. clear H3.
  assert (v = n - minpremk)%nat. lia. subst v.
  specialize (minsleq _ inprem). cbn in minsleq. rewrite H4 in minsleq.
  rewrite H1 in minsleq. depelim minsleq. lia.
Qed.

Definition model_above cls m := forall l,
  LevelSet.In l (clauses_levels cls) ->
  exists k', LevelMap.MapsTo l k' m /\ max_clause_premise cls <= k'.

Lemma model_above_infers {cls m} :
  model_above cls m ->
  (forall l, LevelSet.In l (clauses_levels cls) -> infers_atom m l (max_clause_premise cls)).
Proof.
Admitted.

Lemma model_above_update {cls V' m m'} :
  model_above cls m ->
  strictly_updates cls V' m m' ->
  model_above cls m'.
Proof.
  move=> above /strictly_updates_ext.
  move=> le l /above => [] [] k' [] hm hle.
  apply le in hm as [k'' [hin' le']].
  exists k''. split => //. now transitivity k'.
Qed.

Lemma max_premise_model_above cls m : max_premise_model cls clauses_levels m -> model_above cls m.
Admitted.

Lemma strictly_updates_entails {cls V mzero m} (hne : ~ LevelMap.Empty mzero) (hne' : ~ LevelMap.Empty m) :
  strictly_updates cls V mzero m ->
  entails_all cls (of_level_map mzero hne) (of_level_map m hne').
Proof.
  intros su; induction su.
  - destruct cl as [prems [concl k]].
    destruct H0 as [minp [hmin hlt nabove eqm']].
    have [minsleq mineq] := min_premise_spec m prems.
    destruct mineq as [minprem [inprems eqminp]]. cbn.
    move: eqminp. rewrite /min_atom_value.
    move/negbTE/level_value_not_above_spec: nabove => nabove.
    destruct minprem as [minprem mink].
    destruct (level_value m minprem) eqn:hminprem; rewrite hmin //; intros [= ->].
    intros [l k'] hin.
    eapply of_level_map_spec in hin. rewrite eqm' in hin.
    rewrite LevelMapFact.F.add_mapsto_iff in hin.
    destruct hin as [[eq heq]|[neq hm]]. subst k'.
    have hypss := of_level_map_spec m hne.
    set (hyps := of_level_map m hne) in *. clearbody hyps.
    have entailscl : entails cls (prems, (concl, k)) by exact: entails_in H.
    move/(entails_shift (n - mink)%nat): entailscl. cbn. move => entailscl.
    eapply (entails_all_one (concl := add_prems (n - mink) prems)) => //.
    eapply level_value_MapsTo' in hminprem.
    rewrite -hypss in hminprem.
    eapply hyps_entails; tea.
    rewrite hmin. lia_f_equal.
    have -> : k + Z.to_nat (Z.of_nat n - Z.of_nat mink) = k + (n - mink) by lia. now red in eq; subst concl.
    constructor. now rewrite of_level_map_spec.
  - have hnemid : ~ LevelMap.Empty m'. by exact: strictly_updates_non_empty_map su1.
    specialize (IHsu1 hne hnemid).
    specialize (IHsu2 hnemid hne').
    eapply entails_all_trans; tea.
Qed.

Lemma not_empty_exists V : ~ LevelSet.Empty V -> exists l, LevelSet.In l V.
Proof.
  intros ne.
  destruct (LevelSet.choose V) eqn:ch. exists e.
  now eapply LevelSet.choose_spec1 in ch.
  now apply LevelSet.choose_spec2 in ch.
Qed.

Lemma of_level_map_of_level_set cls sel V m hne hne' :
  max_premise_model cls sel m ->
  V =_lset sel cls ->
  of_level_map m hne = of_level_set V (max_clause_premise cls) hne'.
Proof.
  move=> mp hv. apply: eq_univ' => [[l k]].
  rewrite of_level_map_spec levelexprset_of_levels_spec.
  split. red in mp.
  move/(proj2 mp l) => [hin eq]. split. 2:lia. lsets.
  move=> [] inl ->. rewrite hv in inl.
  now apply mp.
Qed.

Lemma infers_atom_of_level_map {cls m hne l k} :
  infers_atom m l k ->
  cls ⊢ of_level_map m hne → (l, k).
Proof.
  rewrite /infers_atom. intros hle. depelim hle.
  have [y' eq] : exists y', y = (k + y'). exists (y - k). lia.
  eapply (entails_trans (concl := (l, k + y'))).
  - constructor. rewrite of_level_map_spec.
    eapply level_value_MapsTo'. rewrite H0. f_equal. lia.
  - eapply (entails_pred_closure_n (n := y')).
    constructor. now eapply LevelExprSet.singleton_spec.
Qed.

Lemma of_level_map_entails_of_level_set cls V m hne hne' :
  above_max_premise_model cls m ->
  V ⊂_lset clauses_levels cls ->
  cls ⊢a of_level_map m hne → of_level_set V (max_clause_premise cls) hne'.
Proof.
  move=> mp hv.
  intros [l k].
  rewrite levelexprset_of_levels_spec.
  intros [hin ->].
  have hi := above_max_premise_model_infers mp.
  move: (hi l (hv _ hin)).
  eapply infers_atom_of_level_map.
Qed.

(*
Lemma of_level_set_entails_of_level_map cls sel V m hne hne' :
  above_max_premise_model cls sel m ->
  V ⊂_lset sel cls ->
  cls ⊢a of_level_set V (max_clause_premise cls) hne' → of_level_map m hne.
Proof.
  move=> mp hv.
  intros [l k].
  rewrite of_level_map_spec. levelexprset_of_levels_spec.
  intros [hin ->].
  move: (mp l (hv _ hin)).
  eapply infers_atom_of_level_map.
Qed. *)

(* The criterion for loops:
  when a set of updates manages to strictly update all the levels it started with,
  then we can deduce a looping constraint `x, ..., z -> x + 1, ... z + 1`.

  TODO: refine the premises, this should work also when some clauses cannot be considered,
  so that it can be used for checking and not only inferrence.

  *)

Lemma max_premise_model_unique cls m : max_premise_model cls clauses_levels m -> m = max_premise_map cls.
Proof.
Admitted.

Lemma strictly_updates_entails_loop cls V (hne : ~ LevelSet.Empty V) mzero m :
  max_premise_model cls clauses_levels mzero ->
  V =_lset clauses_levels cls ->
  model_of V mzero ->
  strictly_updates cls V mzero m ->
  entails_all cls (of_level_set V (max_clause_premise cls) hne)
    (of_level_set V (max_clause_premise cls + 1) hne).
Proof.
  intros maxp vincl tot su.
  have mp := strictly_updates_model_lt su tot.
  have nemzero : ~ LevelMap.Empty mzero.
  { have := not_empty_exists V hne => [[l]].
    now move/tot => [v hm] /(_ _ _ hm). }
  have nem := strictly_updates_non_empty_map su.
  eapply (strictly_updates_entails nemzero nem) in su; tea.
  unshelve erewrite of_level_map_of_level_set in su; tea.
  move/entails_all_trans: su; apply.
  apply: entails_succ => l k.
  rewrite levelexprset_of_levels_spec => [[hin ->]].
  rw of_level_map_spec.
  move: (mp l) => [] /(_ hin).
  move: (tot _ hin) => [x hm].
  move/(_ _ hm) => [k' [hm' lt]].
  intros _.
  exists k'.
  unfold max_premise_model in maxp.
  move: (proj1 maxp l) => hl.
  forward hl. apply vincl, hin.
  eapply LevelMapFact.F.MapsTo_fun in hm; tea. noconf hm.
  split => //. lia.
Qed.

Lemma strictly_updates_entails_loop_above_max cls V (hne : ~ LevelSet.Empty V) mzero m :
  above_max_premise_model cls mzero ->
  V =_lset clauses_levels cls ->
  model_of V mzero ->
  strictly_updates cls V mzero m ->
  entails_all cls (of_level_set V (max_clause_premise cls) hne)
    (of_level_set V (max_clause_premise cls + 1) hne).
Proof.
  move=> habove hv tot su.
  destruct habove as [[V' ha]|eq].
  * apply (strictly_updates_entails_loop cls V hne (max_premise_map cls) m); tea.
    - apply max_premise_model_exists.
    - have [hs hs'] := max_premise_model_exists cls. red.
      intros k hm. rewrite hv in hm. specialize (hs _ hm). now eexists.
    - have tr := strictly_updates_trans ha su. rewrite union_idem in tr.
      eapply strictly_updates_incl in ha.
      assert (V' ∪ V = V).
      { apply LevelSet.eq_leibniz. red.
        rewrite hv. move: (clauses_conclusions_levels cls). lsets. }
      now rewrite H in tr.
  * subst mzero.
    eapply strictly_updates_entails_loop; tea.
    apply max_premise_model_exists.
Qed.

(*
Lemma strictly_updates_restrict cls V m m' :
  strictly_updates cls V m m' ->
  (forall cl, Clauses.In cl (cls_diff cls V) -> valid_clause m cl) ->
  strictly_updates (cls ⇂ V) V m m'.
Proof.
  induction 1.
  - intros hcl. constructor; auto.
    move: {hcl} (hcl cl).
    rewrite Clauses.diff_spec in_clauses_with_concl in_restrict_clauses.
    destruct cl as [prems [concl k]]; cbn.
    move=> h. split => //. eapply in_singleton.
    forward h.
    { split. split => //. apply in_singleton.
    intros [insing hle incl'].
    assert (~ LevelSet.Empty (levels prems)). admit.
    have eqc : (forall l, LevelSet.In l (levels prems) -> l = concl).
    { move=> l /hle. now rewrite LevelSet.singleton_spec. }
    move: H0; rewrite /valid_clause //=.
    intros [v [hmin hlt la eqm]].
    destruct min_premise eqn:hm => //.
    have [minple [minprem [inprems eqm]]] := min_premise_spec m prems.


    assert (LevelSet.Equal (levels prems) (LevelSet.singleton concl)). split => //. lsets.
    rewrite LevelSet.singleton_spec => ->. destruct (LevelSet.choose (levels prems)) eqn:hc.
    apply LevelSet.choose_spec1 in hc. apply hle in hc. apply LevelSet.singleton_spec in hc; red in hc; subst.

*)


Definition new_model m V newk : model :=
  LevelMap.fold (fun l k acc =>
    let k' := if LevelSet.mem l V then newk else k in
    LevelMap.add l k' acc) m (LevelMap.empty _).

Lemma new_model_spec m V newk l k :
  LevelMap.MapsTo l k (new_model m V newk) ->
  (exists k', LevelMap.MapsTo l k' m /\
    if LevelSet.mem l V then k = newk else k = k').
Proof. Admitted.

Definition domain (l : LevelMap.t (option Z)) : LevelSet.t :=
  LevelSetProp.of_list (List.map fst (LevelMap.elements l)).

(* Lemma level_value_new_model {m V newk l} :
  model_of V m ->
  level_value (new_model m V newk) l =
  if LevelSet.mem l V then newk else level_value m l.
Admitted. *)

(* Lemma strictly_updates_entails_loop2 cls V (hne : ~ LevelSet.Empty V) mzero m :
  let bound := v_minus_w_bound V m in
  let maxgain := max_gain cls in
  let n := Z.to_nat bound + maxgain in
  (* V =_lset clauses_levels cls -> *)
  model_of V mzero ->
  strictly_updates cls V mzero m ->
  entails_all cls (of_level_set V n hne) (of_level_set V (n + 1) hne).
Proof.
  intros bound maxgain n tot su.
  have nemzero : ~ LevelMap.Empty mzero.
  { have := not_empty_exists V hne => [[l]].
    now move/tot => [v hm] /(_ _ _ hm). }
  have nem := strictly_updates_non_empty_map su.
  (* eapply strictly_updates_strenghten in su. *)
  (* unshelve eapply strictly_updates_entails in su; tea. *)
  set (m' := new_model m V (Some (Z.of_nat n))).
  set (d := LevelSet.diff (domain mzero) V).
  have vm : is_model (cls ↓ d) m'.
  { eapply Clauses.for_all_spec. tc. intros cl hin.
    unfold valid_clause. destruct min_premise eqn:hmin => //.
    destruct cl as [prems [concl k]]. cbn in *.
    elim: Z.ltb_spec => // ge //=. unfold level_value_above.
    destruct level_value eqn:hl => //. eapply level_value_MapsTo' in hl.
    apply new_model_spec in hl as [k' [hm cond]].
    destruct LevelSet.mem eqn:hmem. noconf cond. admit. subst k'.
    have [minple minpeq] := min_premise_spec m' prems.
    destruct minpeq as [[minpl minpk] [inminp mineq]].
    destruct (inLevelSet V minpl).
    3:{ admit. }
    (* clause has its minimal premise in V which might have been updated in m.
        In m' its value is hence n *)
    unfold min_atom_value in mineq.
    rewrite level_value_new_model in mineq => //. now eapply strictly_updates_total_model.
    rewrite (LevelSetFact.mem_1 H) in mineq.
    rewrite hmin in mineq. noconf mineq.


    }


  have [m'' su'] : exists m'', strictly_updates (cls ⇂ V) V m' m''.
  admit.
  have mp := strictly_updates_model_lt su'.
  forward mp. admit.
  eapply entails_all_clauses_subset.
  have nem' : ~ LevelMap.Empty m'. admit.
  have nem'' : ~ LevelMap.Empty m''. admit.

  (* have sue := strictly_updates_entails nem' nem'' _ su'. *)
  (* forward sue. admit. apply sue in su'. (cls ⇂ V). in su'; tea *)
Admitted. *)


Lemma model_max_max_premise_map cls : (model_max (max_premise_map cls)) = max_clause_premise cls.
Proof.
Admitted.

Lemma strictly_updates_entails_loop_max cls V (hne : ~ LevelSet.Empty V) m :
  V =_lset clauses_levels cls ->
  strictly_updates cls V (max_premise_map cls) m ->
  entails_all cls (of_level_set V ((model_max (max_premise_map cls))) hne)
    (of_level_set V ((model_max (max_premise_map cls)) + 1) hne).
Proof.
  intros.
  rewrite !model_max_max_premise_map.
  eapply strictly_updates_entails_loop; tea.
  eapply max_premise_model_exists.
  apply todo.
Qed.

#[program]
Definition of_level_map_n (m : LevelMap.t nat) V n (hne : ~ LevelMap.Empty m) : nonEmptyLevelExprSet :=
  {| t_set := LevelMap.fold (fun l k acc =>
    if LevelSet.mem l V then LevelExprSet.add (l, n + k) acc else
    LevelExprSet.add (l, k) acc) m LevelExprSet.empty |}.
Next Obligation. Admitted.

Lemma of_level_map_n_spec m V hne :
  forall l n k, LevelExprSet.In (l, k) (of_level_map_n m V n hne) ->
    (exists k', LevelMap.MapsTo l k' m /\
      (LevelSet.In l V -> k = n + k') /\
      (~ LevelSet.In l V -> k = k')).
Proof.
Admitted.

Lemma of_level_map_n_spec_inv m V hne :
  forall l n k, LevelMap.MapsTo l k m ->
    exists k', LevelExprSet.In (l, k') (of_level_map_n m V n hne) /\
      (LevelSet.In l V -> k' = n + k) /\
      (~ LevelSet.In l V -> k' = k).
Proof.
Admitted.

Lemma entails_any_one V cls m nem m' nem' :
  model_of V m ->
  cls ⊢a of_level_map m nem → of_level_map m' nem' ->
  model_rel_partial Nat.lt V m m' ->
  forall l k, LevelSet.In l V ->
  LevelMap.MapsTo l k m -> cls ⊢ of_level_map m nem → (l, k + 1).
Proof.
  intros tot cla mp l k hin hm.
  eapply entails_all_one; tea.
  move: (proj1 (mp l) hin).
  move: (tot _ hin) => [x hm'].
  move/(_ _ hm) => [k'' [hm'' lt]].
  apply infers_atom_of_level_map. red. rewrite (level_value_MapsTo hm''). constructor. lia.
Qed.

Lemma of_level_map_of_level_map_n m V ne :
  of_level_map m ne = of_level_map_n m V 0 ne.
Proof.
  apply eq_univ'.
  intros [l k].
  rewrite of_level_map_spec.
  firstorder.
  - unshelve eapply (of_level_map_n_spec_inv _ V ne _ 0) in H.
    destruct H as [k' [hin [inv ninv]]].
    destruct (inLevelSet V l) as [hvin|hnin].
    specialize (inv hvin). cbn in inv. now subst k'.
    specialize (ninv hnin). cbn in ninv. now subst.
  - eapply of_level_map_n_spec in H as [k' [hm [hin hnin]]].
    destruct (inLevelSet V l) as [hvin|hvnin].
    now rewrite (hin hvin).
    now rewrite (hnin hvnin).
Qed.

Lemma of_level_map_n_only_model m V n ne :
  only_model_of V m ->
  of_level_map_n m V n ne = add_prems n (of_level_map m ne).
Proof.
  intros om.
  apply eq_univ'.
  intros [l k].
  rewrite In_add_prems.
  split.
  - move/of_level_map_n_spec => [k' [hm [hin hnin]]].
    destruct (inLevelSet V l) as [hvin|hvnin].
    * rewrite (hin hvin). exists (l, k').
      rewrite of_level_map_spec. split => //. rewrite /add_expr. lia_f_equal.
    * elim hvnin. apply om. now exists k'.
  - intros [[? ?] [hin heq]]. unfold add_expr in heq; noconf heq.
    unshelve eapply of_level_map_spec in hin.
    have inv : LevelSet.In l V.
    { apply om. now exists n0. }
    eapply (of_level_map_n_spec_inv _ V ne _ n) in hin as [k' [hin [hinv hninv]]].
    specialize (hinv inv). subst k'. now rewrite Nat.add_comm.
Qed.

Lemma entails_any V cls m nem m' nem' :
  model_of V m ->
  cls ⊢a of_level_map m nem → of_level_map m' nem' ->
  model_rel_partial Nat.lt V m m' ->
  cls ⊢a of_level_map m nem → of_level_map_n m V 1 nem.
Proof.
  intros tot cla mp [l k].
  move/of_level_map_n_spec.
  intros [k' [hm [hin hnin]]].
  destruct (LevelSetDecide.MSetDecideAuxiliary.dec_In l V).
  rewrite (hin H).
  rewrite -[1 + _]Nat.add_1_r.
  eapply entails_any_one; tea.
  rewrite (hnin H).
  constructor. now rewrite of_level_map_spec.
Qed.

(* Lemma entails_any V cls m nem m' nem' :
  model_of V m ->
  model_rel_partial Z.lt V m m' ->
  cls ⊢a of_level_map_n m V 1 nem → of_level_map_n m V 2 nem.
Proof. *)

Lemma strictly_updates_entails_on_V cls V mzero hne m :
  model_of V mzero ->
  strictly_updates cls V mzero m ->
  entails_all (cls ↓ V) (of_level_map mzero hne) (of_level_map_n mzero V 1 hne).
Proof.
  move=> tot su.
  have mp := strictly_updates_model_lt su tot.
  have nem := strictly_updates_non_empty_map su.
  eapply strictly_updates_strenghten in su.
  eapply (strictly_updates_entails hne nem) in su; tea.
  eapply entails_any in su; tea.
Qed.

(* Lemma entails_concls cls V n m hne hne' :
  model_of V m ->
  entails_all cls (of_level_map_n m V n hne) (of_level_set V n hne').
Proof.
  move=> tot [l k].
  rewrite levelexprset_of_levels_spec => [] [] hin ->.
  specialize (tot _ hin) as [k' hm].
  move/of_level_map_n_spec_inv in hm.
  specialize (hm V hne n) as [k'' [hm [hin' hnin]]].
  specialize (hin' hin). subst k''. cbn in *.
  exists
  depind ent.
  - move: H.
    rewrite of_level_map_n_spec => [] [k' [mt [hin hnin]]].
    destruct (inLevelSet V l) as [H|H].
    * now left.
    * right. apply hnin in H. now subst k'.
  - specialize (IHent _ _ _ en l).

  intros [] *)

(*
Lemma strictly_updates_entails_loop_relax cls V mzero hne m :
  let bound := v_minus_w_bound V m in
  let maxgain := max_gain cls in
  let n := Z.to_nat bound + maxgain in
  model_of V mzero ->
  strictly_updates cls V mzero m ->
  entails_all cls (of_level_map_n mzero V n hne) (of_level_map_n mzero V (n + 1) hne).
Proof.
  move=> bound maxgain n tot su.
  have mp := strictly_updates_model_lt su tot.
  have nem := strictly_updates_non_empty_map su.
  eapply (strictly_updates_entails hne nem) in su; tea.
  eapply entails_any in su; tea.
  eapply (entails_all_shift n) in su.
  rewrite -of_level_map_of_level_map_n.
Qed.
*)
(* Lemma of_level_map_n_split m V n hne : of_level_map_n m V n hne = of_level_set V n hne'  *)

(*
Lemma strictly_updates_entails_loop_relax' ocls cls V (hne : ~ LevelSet.Empty V) mzero m :
  above_max_premise_model ocls mzero ->
  cls ⊂_clset ocls ->
  V =_lset clauses_levels cls ->
  model_of V mzero ->
  strictly_updates cls V mzero m ->
  entails_all cls (of_level_set V (max_clause_premise cls) hne)
    (of_level_set V (max_clause_premise cls + 1) hne).
Proof.
  move=> habove hincl hv tot su.
  eapply strictly_updates_entails_loop_relax; tea. *)




Lemma add_prems_add {n lk prems} : add_prems n (add lk prems) = add (add_expr n lk) (add_prems n prems).
Proof.
  apply eq_univ'. intros x.
  rewrite In_add_prems LevelExprSet.add_spec In_add_prems /LevelExprSet.E.eq; rw LevelExprSet.add_spec.
  firstorder. subst. red in H; subst x0. now left.
Qed.
(*
Lemma above_max_premise_model_strengthen {cls cls' m} :
  cls ⊂_clset cls' ->
  above_max_premise_model cls m ->
  above_max_premise_model cls' m.
Proof.
  intros hincl [[V' su]|eq].
  left. 2:{ subst. red. } exists V'.
  eapply strictly_updates_weaken; tea. red in ha.
  move/(hmon _ _ hincl)/(ha l) => ha'.
  eapply infer_atom_downward; tea.
  apply max_clause_premise_mon in hincl. lia.
Qed. *)

Lemma add_prems_of_level_set k W k' prf :
  add_prems k (of_level_set W k' prf) = of_level_set W (k + k') prf.
Proof.
  apply eq_univ' => [] [l n].
  rewrite In_add_prems /of_level_set //= levelexprset_of_levels_spec.
  split.
  - move=> [] [l' n']. rewrite levelexprset_of_levels_spec => [] [[inw eq] eq'].
    subst n'. noconf eq'. split => //. lia.
  - move=> [inW ->]. exists (l, k'). rewrite levelexprset_of_levels_spec.
    split => //. cbn. f_equal; lia.
Qed.

Lemma of_level_set_singleton l k hne : of_level_set (LevelSet.singleton l) k hne = singleton (l, k).
Proof.
  apply: eq_univ'. move=> [l' k'].
  rewrite /of_level_set //= levelexprset_of_levels_spec !LevelExprSet.singleton_spec LevelSet.singleton_spec /LevelSet.E.eq /LevelExprSet.E.eq.
  firstorder subst => //. now noconf H. now noconf H.
Qed.

Lemma entails_of_level_set_strenghten cls W k' k prf :
  k' <= k ->
  cls ⊢a of_level_set W k' prf → of_level_set W (k' + 1) prf ->
  cls ⊢a of_level_set W k prf → of_level_set W (k + 1) prf.
Proof.
  intros le ea.
  have := entails_all_shift (k - k') ea.
  rewrite !add_prems_of_level_set.
  have -> : k - k' + k' = k by lia.
  now have -> : k - k' + (k' + 1) = k + 1 by lia.
Qed.

Lemma strictly_updates_non_empty_init_map {cls W m m'} :
  strictly_updates cls W m m' -> ~ LevelMap.Empty m.
Proof.
  induction 1.
  - destruct cl as [prems [concl k]].
    destruct H0 as [? [? ? ? heq]].
    eapply min_premise_spec_aux in H0 as [_ [[] [inprems heq']]].
    unfold min_atom_value in heq'.
    destruct level_value eqn:hl => //. apply level_value_MapsTo' in hl.
    now intros e; apply e in hl.
  - auto.
Qed.

Lemma check_model_ne_init_map {cls V U minit m W m'} :
  [/\ clauses_levels cls ⊂_lset V, only_model_of V minit & is_update_of cls U minit m] ->
  check_model cls (U, m) = Some (W, m') ->
  ~ LevelMap.Empty minit.
Proof.
  intros [_ _ isupd] check.
  eapply check_model_is_update_of in check as [su incl]; tea.
  rewrite union_idem in su.
  now eapply strictly_updates_non_empty_init_map in su.
Qed.

Lemma check_model_ne_map {cls U m W m'} :
  check_model cls (U, m) = Some (W, m') ->
  ~ LevelMap.Empty m'.
Proof.
  intros check.
  eapply check_model_spec in check as [W' [su incl]]; tea.
  now eapply strictly_updates_non_empty_map in su.
Qed.

Lemma only_model_of_model_of {V m} : only_model_of V m -> model_of V m.
Proof.
  intros om l. move/om. intros [k hm]; now exists k.
Qed.

Coercion only_model_of_model_of : only_model_of >-> model_of.

#[tactic="idtac"]
Equations? loop (V : LevelSet.t) (U : LevelSet.t) (cls : clauses) (minit m : model)
  (prf : [/\ clauses_levels cls ⊂_lset V, only_model_of V minit & is_update_of cls U minit m]) : result V U cls minit
  by wf (loop_measure V U) lexprod_rel :=
  loop V U cls minit m prf with inspect (check_model cls (U, m)) :=
    | exist None eqm => Model U {| model_model := m |} _
    | exist (Some (W, m')) eqm with inspect (LevelSet.equal W V) := {
      | exist true eq := Loop (of_level_map minit (check_model_ne_init_map prf eqm)) _
      (* Loop on cls ↓ W, with |W| < |V| *)
      | exist false neq with inner_loop V U minit loop W (cls ↓ W) m' _ :=
        { | Loop u isloop := Loop u (loop_on_subset _ isloop)
          | Model Wc mwc _
          (* We get a model for (cls ↓ W), we check if it extends to all clauses.
              By invariant |Wc| cannot be larger than |W|. *)
            with inspect (check_model cls (Wc, mwc.(model_model))) :=
          { | exist None eqm' => Model (LevelSet.union W Wc) {| model_model := mwc.(model_model) |} _
            | exist (Some (Wcls, mcls)) eqm' with inspect (LevelSet.equal Wcls V) := {
              | exist true _ := Loop (of_level_map m' (check_model_ne_map eqm)) _
              | exist false neq' with loop V (LevelSet.union W Wcls) cls minit mcls _ := {
                (* Here Wcls < V, we've found a model for all of the clauses with conclusion
                  in W, which can now be fixed. We concentrate on the clauses whose
                  conclusion is different. Clearly |W| < |V|, but |Wcls| is not
                  necessarily < |V| *)
                  | Loop u isloop := Loop u isloop
                  | Model Wvw mcls' hsub := Model Wvw {| model_model := model_model mcls' |} _ } } }
          }
      }
    .
Proof.
  all:cbn -[cls_diff clauses_with_concl restrict_clauses]; clear loop.
  all:try solve [intuition auto].
  all:try eapply levelset_neq in neq.
  all:have cls_sub := clauses_conclusions_levels cls.
  all:destruct prf as [clsV mof isupd].
  - red. eapply LevelSet.equal_spec in eq.
    set (prf := check_model_ne_init_map _ _); clearbody prf.
    eapply check_model_is_update_of in eqm; tea. rewrite eq in eqm.
    destruct eqm as [eqm incl]. rewrite union_idem in eqm.
    unshelve eapply strictly_updates_entails_on_V in eqm; tea.
    rewrite of_level_map_n_only_model in eqm => //.
    eapply entails_all_clauses_subset; tea. apply clauses_with_concl_subset. exact mof.
  - eapply check_model_is_update_of in eqm as [eqm incl]; tea.
    have hi := strictly_updates_incl eqm.
    rewrite union_idem in hi, eqm.
    split => //.
    * split => //. lsets.
    * now eapply strictly_updates_non_empty.
    * apply clauses_conclusions_clauses_with_concl.
    * eapply strictly_updates_strenghten. exact eqm.

  - now intros ?; rewrite in_clauses_with_concl.
  - set (ne := check_model_ne_map _). clearbody ne.
    have hu := model_updates mwc.
    eapply check_model_is_update_of in eqm as [eqm incl]; tea.
    have om : only_model_of V m'.
    { rewrite union_idem in eqm.
      have incl' := strictly_updates_incl eqm.
      have hcl := clauses_conclusions_levels cls.
      eapply strictly_updates_only_model_gen in eqm; tea. eapply only_model_of_eq; tea. intro; lsets. }
    eapply strictly_updates_is_update_of in eqm; tea.
    rewrite union_idem union_with_concl in eqm.
    eapply check_model_is_update_of in eqm' as [eqm' incl']; tea.
    rewrite ClausesProp.union_sym union_with_concl in eqm'.
    eapply (strictly_updates_entails_on_V _ _ _ ne) in eqm'. red.
    rewrite of_level_map_n_only_model in eqm'. eapply LevelSet.equal_spec in e. now rewrite e.
    eapply entails_all_clauses_subset; tea.
    eapply clauses_with_concl_subset. apply LevelSet.equal_spec in e. rewrite e. exact om.
  - eapply check_model_is_update_of in eqm as [eqm incl]; tea.
    have hu := model_updates mwc.
    eapply strictly_updates_is_update_of in hu; tea.
    rewrite union_idem union_with_concl in hu.
    eapply check_model_update_of in eqm' as [wmcls [upd ->]].
    eapply is_update_of_strictly_updates in hu.
    have tr := is_update_of_trans_eq hu upd.
    split => //. apply tr. clsets. lsets.
  - right.
    eapply check_model_spec_V in eqm' as eqm''. 3:etransitivity; [apply clauses_conclusions_levels|exact clsV]. cbn in eqm''.
    2:{
      eapply check_model_is_update_of in eqm as [eqm incl]; tea. rewrite union_idem in eqm.
      eapply strictly_updates_is_update_of in eqm; tea. 2:apply mwc.
      eapply strictly_updates_model_of_gen in eqm; tea. 2:exact mof.
      eapply model_of_subset; tea. lsets. }
    2:{ eapply is_update_of_total_model. apply mwc. }
    destruct eqm'' as [Hwc Hwcls H1 mext tot].
    eapply check_model_is_update_of in eqm as [eqm incl]; tea.
    rewrite union_idem in eqm.
    have hu := model_updates mwc.
    eapply check_model_is_update_of in eqm' as [eqm' incl']; tea.
    rewrite ClausesProp.union_sym union_with_concl in eqm'.
    have WcW := model_incl mwc.
    (* destruct hsub' as [UWc WcW]. *)
    have w_incl := strictly_updates_incl eqm.
    have wcls_incl := strictly_updates_incl eqm'.
    assert (exists l, LevelSet.In l Wcls /\ ~ LevelSet.In l W).
    { destruct H1 as [cl [clcls nvalid hcll hv]].
      pose proof (model_ok mwc).
      eapply is_model_invalid_clause in H; tea.
      assert (~ LevelSet.In (levelexpr_level (concl cl)) W).
      { intros hin. rewrite in_clauses_with_concl in H. intuition auto. }
      exists (concl cl). split => //. }
    rewrite -!diff_cardinal //. clear -w_incl clsV incl wcls_incl. have hincl := clauses_conclusions_levels cls. lsets. lsets.
    assert (Wcls ⊂_lset V). lsets.
    eapply strict_subset_cardinal.
    eapply (strict_subset_leq_right _ (LevelSet.diff V W)). 2:lsets.
    apply strict_subset_diff_incl => //.
    { red. split => //. lsets. intros heq. destruct H as [l' [hin hnin]].
      rewrite heq in hnin. apply hnin. lsets. }
    lsets. lsets.
  - eapply mcls'.
  - apply mcls'.
  - apply mcls'.
  - apply mcls'.
  - eapply check_model_is_update_of in eqm as []; tea. lsets.
  - eapply check_model_is_update_of in eqm as [suinit incl]; tea. rewrite union_idem in suinit.
    have hupd := model_updates mwc.
    eapply (is_update_of_weaken (cls' := cls)) in hupd. 2:intros ? ; rewrite in_clauses_with_concl; clsets.
    eapply strictly_updates_is_update_of in suinit; tea. rewrite union_idem in suinit.
    eapply model_of_strictly_updates; tea. exact mof.
  - eapply check_model_is_update_of in eqm as [suinit incl]; tea. rewrite union_idem in suinit.
    have hupd := model_updates mwc.
    eapply (is_update_of_weaken (cls' := cls)) in hupd. 2:intros ? ; rewrite in_clauses_with_concl; clsets.
    eapply is_update_of_trans_eq. eapply is_update_of_strictly_updates. tea. tea. clsets. lsets.
  - eapply clauses_levels_conclusions; assumption.
  - now apply check_model_None in eqm'.
  - eapply check_model_is_update_of in eqm as [suinit incl]; tea. lsets.
  - move: isupd. rewrite /is_update_of.
    destruct LevelSet.is_empty.
    * intros <-. exact mof.
    * intros su.
      eapply model_of_strictly_updates; tea. exact mof.
  - exact isupd.
  - apply clauses_levels_conclusions. assumption.
  - now eapply check_model_None in eqm.
  - lsets.
Qed.

Transparent lexprod_rel_wf.

Lemma add_prems_0 u : add_prems 0 u = u.
Proof.
  rewrite /add_prems.
  apply eq_univ'.
  intros x. rewrite map_spec.
  split.
  - intros[e [hin ->]]. unfold add_expr. now destruct e; rewrite Nat.add_0_r.
  - intros inu; exists x. split => //. destruct x. now rewrite /add_expr Nat.add_0_r.
Qed.

Lemma entails_all_tauto cls u : cls ⊢a u → u.
Proof.
  intros x hin. now constructor.
Qed.

Lemma loop_any_successor cls u n :
  cls ⊢a u → succ_prems u ->
  cls ⊢a u → add_prems (S n) u.
Proof.
  induction n.
  - auto.
  - intros ass.
    specialize (IHn ass).
    have sh := entails_all_shift 1 IHn.
    eapply entails_all_trans. tea.
    now rewrite add_prems_add_prems in sh.
Qed.

Lemma loop_any cls u n :
  cls ⊢a u → succ_prems u ->
  cls ⊢a u → add_prems n u.
Proof.
  destruct n.
  - rewrite add_prems_0. intros _. apply entails_all_tauto.
  - apply loop_any_successor.
Qed.

Lemma univ_non_empty (u : univ) : ~ LevelSet.Empty (levels u).
Proof. intros he. have := t_ne u. move/not_Empty_is_empty.
  intros he'. apply he'. intros [l k] hin. red in he. specialize (he l). apply he.
  rewrite levelexprset_levels_spec. now exists k.
Qed.

Lemma loop_max cls (u : univ) :
  cls ⊢a of_level_set (levels u) (premise_max u) (univ_non_empty u) → u.
Proof.
  intros [l k] hin.
  apply (entails_pred_closure_n (n := premise_max u - k)).
  constructor.
  rewrite levelexprset_of_levels_spec. split.
  - apply levelexprset_levels_spec. now exists k.
  - have [min _] := premise_max_spec u.
    apply min in hin. cbn in hin. lia.
Qed.

Lemma loop_any_max cls u n :
  cls ⊢a u → add_prems n u ->
  cls ⊢a of_level_set (levels u) (premise_max u) (univ_non_empty u) → add_prems n u.
Proof.
  intros hl. eapply entails_all_trans; tea. now eapply loop_max.
Qed.

Lemma loop_any_max_all cls u :
  cls ⊢a u → succ_prems u ->
  cls ⊢a of_level_set (levels u) (premise_max u) (univ_non_empty u) →
    of_level_set (levels u) (premise_max u + 1) (univ_non_empty u).
Proof.
  intros hl. eapply entails_all_trans; tea.
  eapply (loop_any_max _ _ (premise_max u + 1)). now eapply loop_any.
  intros [l k].
  rewrite levelexprset_of_levels_spec => [] [].
  rewrite levelexprset_levels_spec => [] [k' hin] ->.
  eapply (entails_pred_closure_n (n := k')).
  constructor. rewrite In_add_prems.
  exists (l, k'). split => //. rewrite /add_expr. lia_f_equal.
Qed.

(* To handle the constraint inference problem,
  we must start with a model where all atoms [l + k]
  appearing in premises are true. Otherwise the
  [l := 0] model is minimal for [l+1-> l+2].
  Starting with [l := 1], we see that the minimal model above it
  has [l := ∞].
  We also ensure that all levels in the conclusions are in the model.
  *)

Definition add_max l k m :=
  match LevelMap.find l m with
  | Some k' =>
    if (k' <? k)%nat then LevelMap.add l k m
    else m
  | _ => LevelMap.add l k m
 end.

Definition min_model_map (m : model) cls : model :=
  Clauses.fold (fun '(cl, concl) acc =>
    LevelExprSet.fold (fun '(l, k) acc =>
      add_max l k acc) cl (add_max (levelexpr_level concl) 0 acc)) cls m.


Lemma In_add_max l l' k acc :
  LevelMap.In (elt:=nat) l (add_max l' k acc) <->
  (l = l' \/ LevelMap.In l acc).
Proof.
  unfold add_max.
  destruct LevelMap.find eqn:hl.
  - case: Nat.ltb_spec.
    + rewrite LevelMapFact.F.add_in_iff /Level.eq.
      firstorder eauto.
    + intros. intuition auto. subst.
      now rewrite LevelMapFact.F.in_find_iff hl.
  - LevelMapFact.F.map_iff. rewrite /Level.eq. intuition auto.
Qed.

Definition is_max k' k l acc :=
  match LevelMap.find l acc with
  | Some k'' => k' = Nat.max k k''
  | _ => k' = k
  end.

Lemma MapsTo_add_max l l' k k' acc :
  LevelMap.MapsTo (elt:=nat) l k' (add_max l' k acc) <->
  if eqb l l' then is_max k' k l acc else LevelMap.MapsTo l k' acc.
Proof.
  unfold add_max.
  destruct LevelMap.find eqn:hl.
  { case: Nat.ltb_spec.
  - rewrite LevelMapFact.F.add_mapsto_iff /Level.eq.
    destruct (eqb_spec l l').
    { unfold is_max.
      firstorder eauto. subst k' l'. rewrite hl. f_equal. lia. congruence. subst l'.
      rewrite hl in H0. subst k'.
      left. split; auto. f_equal; lia. }
    intros. firstorder eauto. congruence.
  - intros. unfold is_max.
    destruct (eqb_spec l l'); subst. rewrite hl. firstorder eauto. apply LevelMap.find_1 in H. rewrite hl in H. noconf H.
    f_equal; lia. subst k'. apply LevelMap.find_2. rewrite hl. f_equal. f_equal. lia. reflexivity.
  }
  - rewrite LevelMapFact.F.add_mapsto_iff. intuition auto; subst.
    destruct (eqb_spec l l'); subst. unfold is_max. now rewrite hl. congruence.
    destruct (eqb_spec l l'); subst. unfold is_max. now rewrite hl. congruence.
    destruct (eqb_spec l l'); subst. unfold is_max in H; rewrite hl in H. subst k'. left; intuition eauto. reflexivity.
    right. intuition eauto.
Qed.

Definition opt_max (x y : option nat) : option nat :=
  match x, y with
  | Some x, Some y => Some (Nat.max x y)
  | None, Some x => Some x
  | Some x, None => Some x
  | None, None => None
  end.

Definition find_max (ls : LevelExprSet.t) (l : Level.t) :=
  LevelExprSet.fold (fun '(l', k) acc => if eqb l l' then opt_max (Some k) acc else acc) ls None.

Inductive find_max_spec ls l : option nat -> Prop :=
| find_max_ex m : LevelExprSet.In (l, m) ls -> (forall k, LevelExprSet.In (l, k) ls -> k <= m) -> find_max_spec ls l (Some m)
| find_max_absent : ~ (exists k, LevelExprSet.In (l, k) ls) -> find_max_spec ls l None.

Lemma find_max_correct ls l : find_max_spec ls l (find_max ls l).
Proof.
  unfold find_max.
  apply: (LevelExprSetProp.fold_rec (P := fun ls a => find_max_spec ls l a)).
  - intros s' ise; constructor. intros [k hin]. now apply ise in hin.
  - intros x a s' s'' hin hnotin hadd hspec.
    destruct x as [l' k].
    destruct (eqb_spec l l'); subst.
    * depelim hspec.
      { constructor. destruct (Nat.max_spec k m) as [[hle hm]|[hle hm]].
        + rewrite hm. apply hadd; right; apply H.
        + rewrite hm. apply hadd; left; reflexivity.
        + intros k' hin'. apply hadd in hin' as [].
          { noconf H1. lia. }
          { specialize (H0 _ H1). lia. } }
      { constructor. apply hadd; now left.
        intros k0 hin'. apply hadd in hin' as [].
        { noconf H0; reflexivity. }
        { elim H. now exists k0. } }
    * depelim hspec; constructor; eauto.
      + apply hadd; now right.
      + intros k' hin'. apply hadd in hin' as [].
        { noconf H2. congruence. }
        now apply H0 in H2.
      + intros [k0 hk0]. apply hadd in hk0 as [].
        { noconf H1; congruence. }
        apply H. now exists k0.
Qed.

Definition update_max acc l k0 :=
  option_map2 Nat.max (level_value acc l) (Some k0).

(* Lemma update_max_spec acc l k : update_max acc l k0 = *)

Definition maximal_pre (l : Level.t) (n : nat) les :=
  forall n', In (l, n') les -> n' <= n.

Definition maximal_map (l : Level.t) (n : nat) m :=
  forall n', LevelMap.MapsTo l (Some n') m -> (n' <= Z.of_nat n)%Z.

Lemma In_fold_add_max k n a :
  LevelMap.In (elt:=nat) k
  (LevelExprSet.fold
      (fun '(l, k0) acc => add_max l k0 acc) n a) <->
  (LevelSet.In k (levels n)) \/ LevelMap.In k a.
Proof.
  eapply LevelExprSetProp.fold_rec.
  - intros s' he.
    rewrite (LevelExprSetProp.empty_is_empty_1 he).
    cbn. unfold levels. rewrite LevelExprSetProp.fold_empty. rewrite LevelSetFact.empty_iff. intuition auto.
  - intros.
    destruct x as [l k'].
    rewrite In_add_max.
    rewrite H2 !levelexprset_levels_spec.
    split.
    * intros []; subst.
      left. exists k'. apply H1. now left.
      destruct H3 as [[k'' ?]|?]. left; exists k''. apply H1. now right.
      now right.
    * red in H1. setoid_rewrite H1.
      intros [[k'' []]|]. noconf H3. now left.
      right. now left; exists k''. right; right. apply H3.
Qed.


Lemma MapsTo_fold_add_max l n a :
  let map := LevelExprSet.fold (fun '(l, k0) acc => add_max l k0 acc) n a in
  (forall k, LevelMap.MapsTo (elt:=nat) l k map ->
  ((exists kl, LevelExprSet.In (l, kl) n /\ kl = k /\
    (forall kl', LevelExprSet.In (l, kl') n -> kl' <= kl) /\
    (forall kl', LevelMap.MapsTo l kl' a -> kl' <= kl)) \/
    (LevelMap.MapsTo l k a /\ (forall kl', LevelExprSet.In (l, kl') n -> kl' <= k))))
  /\ (forall l, ~ LevelMap.In l map -> ~ (exists k, LevelExprSet.In (l, k) n) /\ ~ (LevelMap.In l a)).
Proof.
  eapply LevelExprSetProp.fold_rec.
  - intros s' he. cbn.
    setoid_rewrite (LevelExprSetProp.empty_is_empty_1 he).
    intuition auto. right. split; eauto.
    intros kl. now move/LevelExprSet.empty_spec.
    destruct H0. now apply LevelExprSet.empty_spec in H0.
     (* destruct H0 as [? [he' _]]. now rewrite LevelExprSetFact.empty_iff in he'. *)
  - cbn; intros.
    destruct x as [xl k']. split.
    2:{ intros l0 hnin. destruct H2 as [_ H2]. specialize (H2 l0). split.
      { intros [k hex]. eapply H1 in hex as [hin|hin]. noconf hin. apply hnin.
        eapply In_add_max. now left.
         unshelve eapply (proj1 (H2 _)).
        intros hin'. apply hnin. rewrite In_add_max. now right. now exists k. }
      { apply H2 => hin. elim hnin. rewrite In_add_max. now right. } }
    intros.
    rewrite MapsTo_add_max in H3.
    destruct (eqb_spec l xl); subst.
    * unfold is_max in H3 at 1.
      destruct LevelMap.find eqn:hfind.
      { subst k. pose proof (LevelMap.find_2 hfind). destruct H2 as [H2 Hnotin]. destruct (H2 _ H3).
          left. destruct H4 as [kl [hkl hleq]]. destruct hleq as [hleq hmax]. subst n0.
          destruct (Nat.max_spec k' kl) as [[]|[]].
          { exists kl. split. apply H1. now right. split. f_equal. lia. split. intros.
            apply H1 in H6 as []. noconf H6. lia. now apply (proj1 hmax). destruct hmax as [_ hmax].
            intros. now apply hmax. }
          { exists k'. split. apply H1. now left. split. f_equal; lia. destruct hmax as [hmax hmax']; split.
            intros kl' hin. apply H1 in hin as []; subst. noconf H6. lia. specialize (hmax _ H6). lia.
            intros. transitivity kl. now apply hmax'. lia. }
          destruct (H2 _ H3) as [[kl [hkl hleq]]|]. noconf hleq.
          destruct hleq as [hleq hmax]. subst n0.
          destruct (Nat.max_spec k' kl) as [[]|[]].
          { left. exists kl. split. apply H1. now right. destruct hmax as [hmax hmax']. split. f_equal. lia. split.
            intros. apply H1 in H7 as []. noconf H7. lia. now apply hmax. apply hmax'. }
          { left. exists k'. split. apply H1. now left. destruct hmax as [hmax hmax']. split. f_equal. lia. split.
            intros kl' hin. apply H1 in hin as []. noconf H7. lia. specialize (hmax _ H7). lia.
            intros. transitivity kl => //. now eapply hmax'. }
          destruct H4. clear H5.
          destruct (Nat.max_spec k' n0) as [[]|[]].
          { right. split. now rewrite H7.
            intros kl' hin. apply H1 in hin as [hin|hin]; noconf hin. lia.
            specialize (H6 _ hin). depelim H6; lia. }
          { left. exists k'. split. apply H1. now left. split. f_equal. lia. split.
            intros kl' hin. apply H1 in hin as []. noconf H8. lia.
            specialize (H6 _ H8). lia.
            intros. transitivity n0. 2: lia. eapply (LevelMapFact.F.MapsTo_fun H4) in H8. subst kl'. reflexivity. }
      }
      subst k. left. exists k'. split; eauto. firstorder. split. reflexivity.
      destruct H2 as [hl hnotin]. eapply LevelMapFact.F.not_find_in_iff in hfind.
      apply hnotin in hfind as hfind'.
      split.
      { intros. eapply H1 in H2 as [hin|hin]; noconf hin. reflexivity.
        destruct hfind' as [hfind' _].
        elim hfind'. now exists kl'. }
      { intros kl' hin. destruct hfind' as []. now elim H3; exists kl'. }
    * destruct H2 as [H2 hfind]. destruct (H2 _ H3) as [[lk [hkl hleq]]|].
      + left. depelim hleq. destruct H6 as [hinl hinacc]. exists lk. split; [firstorder|]. split => //.
        split => //.
        { intros kl' hin. apply H1 in hin as [hin|hin]. noconf hin. congruence. subst k. now apply hinl. }
      + right. intuition auto.
        eapply H1 in H5 as [hin|hin]; noconf hin. congruence.
        now eapply H7.
Qed.


Lemma min_model_map_levels m cls k :
  LevelMap.In k (min_model_map m cls) <->
    LevelSet.In k (clauses_levels cls) \/ LevelMap.In k m.
Proof.
  rewrite /min_model_map.
  rewrite clauses_levels_spec.
  eapply ClausesProp.fold_rec.
  - intros s' he. intuition auto.
    destruct H0 as [cl []].
    clsets.
  - intros x a s' s'' inx ninx hadd ih.
    destruct x as [cl k'].
    rewrite In_fold_add_max In_add_max. rewrite ih.
    intuition auto. left. exists (cl, k'); intuition auto.
    apply hadd. now left.
    rewrite clause_levels_spec. now left.
    subst. left. exists (cl, k'). split. apply hadd; now left.
    rewrite clause_levels_spec. now right.
    destruct H as [cl'' []]. left. exists cl''.
    intuition auto. apply hadd. now right.
    destruct H3 as [cl'' []].
    apply hadd in H0 as []; subst.
    rewrite clause_levels_spec in H3. destruct H3; subst.
    cbn in H0. now left. right. now left.
    right. right. left; exists cl''. split => //.
Qed.

Definition maximal_prem l n cls :=
  Clauses.For_all (fun cl => forall n', LevelExprSet.In (l, n') (premise cl) -> n' <= n) cls.

Lemma min_model_mapsto_gen m cls :
  forall l, LevelSet.In l (clauses_levels cls) ->
  exists k, LevelMap.MapsTo l k (min_model_map m cls) /\
  (exists cl, Clauses.In cl cls /\
   exists n, k = n /\ LevelExprSet.In (l,n) (premise cl) /\
   (* (forall cl', Clauses.In cl cls -> forall l k, LevelExprSet.In (l, k) (premise cl') -> k <= n) *)
   maximal_prem l n cls) \/ LevelMap.MapsTo l k m.
Proof.
  rewrite /min_model_map.
  eapply ClausesProp.fold_rec.
  - intros s' he. intuition auto. admit.
  - intros x a s' s'' inx ninx hadd ih.
    destruct x as [prem cl].
    intros.
  Admitted.
(*
    pose proof (MapsTo_fold_add_max l prem (add_max cl 0 a)) as [hf hneq].
    apply hf in H. clear hf.
    destruct H as [[kl [inkl leq]]|].
    { destruct leq as [eq [leqprems leqacc]]; noconf eq.
      destruct (Nat.ltb_spec kl )
      left. exists (prem, cl). split. apply hadd. now left. exists kl.
      split => //. split => //. red.
      intros x hin. apply hadd in hin as []; subst. cbn. exact leqprems.
      intros n hin.
      specialize (ih (Z.of_nat n)). destruct ih as [_ ih].
      forward ih. left. exists x. split => //. exists kl. split => //.
      intros n' hin.
    rewrite In_fold_add_max In_add_max. rewrite ih.
    intuition auto. left. exists (cl, k'); intuition auto.
    apply hadd. now left.
    rewrite clause_levels_spec. now left.
    subst. left. exists (cl, k'). split. apply hadd; now left.
    rewrite clause_levels_spec. now right.
    destruct H as [cl'' []]. left. exists cl''.
    intuition auto. apply hadd. now right.
    destruct H3 as [cl'' []].
    apply hadd in H0 as []; subst.
    rewrite clause_levels_spec in H3. destruct H3; subst.
    cbn in H0. now left. right. now left.
    right. right. left; exists cl''. split => //.
Qed.
*)
Lemma min_model_mapsto cls :
  forall l, LevelSet.In l (clauses_levels cls) ->
  exists k, LevelMap.MapsTo l k (min_model_map (LevelMap.empty _) cls) /\
  (exists cl, Clauses.In cl cls /\
   exists n, k = n /\ LevelExprSet.In (l,n) (premise cl) /\
   (* (forall cl', Clauses.In cl cls -> forall l k, LevelExprSet.In (l, k) (premise cl') -> k <= n) *)
   maximal_prem l n cls).
Proof.
  intros.
  eapply (min_model_mapsto_gen (LevelMap.empty _)) in H as [k []].
  exists k. intuition eauto.
  now eapply LevelMapFact.F.empty_mapsto_iff in H.
Qed.

Definition min_model m cls : model := min_model_map m cls.

Definition init_model cls := min_model (LevelMap.empty _) cls.

Lemma init_model_levels cls k :
  LevelMap.In k (init_model cls) <-> LevelSet.In k (clauses_levels cls).
Proof.
  rewrite min_model_map_levels. intuition auto.
  now rewrite LevelMapFact.F.empty_in_iff in H0.
Qed.

Definition init_w (levels : LevelSet.t) : LevelSet.t := LevelSet.empty.

(* We don't need predecessor clauses as they are trivially satisfied *)
(* Definition add_predecessors (V : LevelSet.t) cls :=
  LevelSet.fold (fun l acc =>
    Clauses.add (NonEmptySetFacts.singleton (l, 1), (l, 0)) acc) V cls. *)

Definition infer_result V cls := result V LevelSet.empty cls (init_model cls).

Equations? infer (cls : clauses) : infer_result (clauses_levels cls) cls :=
  infer cls := loop (clauses_levels cls) LevelSet.empty cls (init_model cls) (init_model cls) (And3 _ _ _).
Proof.
  - reflexivity.
  - intros k. now rewrite -init_model_levels.
  - apply is_update_of_empty.
Qed.

(* Lemma valuation_of_model_pos l k model : LevelMap.MapsTo l (Z.to_nat k) (valuation_of_model model) -> (k >= 0)%Z.
Proof.
  unfold valuation_of_model.
  revert l k.
  eapply LevelMapFact.fold_rec.
  - intros. now rewrite LevelMapFact.F.empty_mapsto_iff in H0.
  - intros l0 k0 e m' m'' me nk hadd hind l k.
    rewrite LevelMapFact.F.add_mapsto_iff.
    intros [].
    * destruct H. red in H; subst.
      destruct k0.
      { have hmax := (model_max_spec model l (Some z) me). depelim hmax.
        have hmin := (model_min_spec model l (Some z) me). depelim hmin.
        assert (0 <= model_max model)%Z. admit.
        assert (model_min model <= 0)%Z. admit.
        assert (model_max model - option_get 0%Z (Some z) - model_min model = k)%Z. admit.
        cbn in H4.
        lia. *)

Local Open Scope string_scope2.

Definition print_level_Z_map (m : LevelMap.t (option Z)) :=
  let list := LevelMap.elements m in
  print_list (fun '(l, w) => Level.to_string l ^ " -> " ^ (match w with None => "undefined" | Some z => string_of_Z z end)) nl list.

Definition print_result {V cls} (m : infer_result V cls) :=
  match m return string with
  | Loop _ _ => "looping on "
  | Model w m _ => "satisfiable with model: " ^ print_level_nat_map m.(model_model) ^ nl ^ " W = " ^
    print_lset w
    ^ nl ^ "valuation: " ^ print_level_nat_map (valuation_of_model m.(model_model))
  end.

Definition valuation_of_result {V cls} (m : infer_result V cls) :=
  match m with
  | Loop _ _  => "looping"
  | Model w m _ => print_level_nat_map (valuation_of_model m.(model_model))
  end.

Definition to_string_expr (e : LevelExpr.t) : string :=
  let '(l, n) := e in Level.to_string l ^ (if n is 0 then "" else "+" ^ string_of_nat n).

Definition print_premise (l : nonEmptyLevelExprSet) : string :=
  let (e, exprs) := NonEmptySetFacts.to_nonempty_list l in
  to_string_expr e ^
  match exprs with
  | [] => ""
  | l => ", " ^ print_list to_string_expr ", " exprs
  end.

Definition print_clauses (cls : clauses) :=
  let list := Clauses.elements cls in
  print_list (fun '(l, r) =>
    print_premise l ^ " → " ^ to_string_expr r) nl list.

Equations? infer_model_extension (V : LevelSet.t) (m : model) (cls cls' : clauses)
  (prf : clauses_levels cls ⊂_lset V /\ clauses_levels cls' ⊂_lset V /\ only_model_of V m) : result V LevelSet.empty (Clauses.union cls cls') m :=
  | V, m, cls, cls', prf := loop V LevelSet.empty (Clauses.union cls cls') m m _.
Proof.
  split.
  - intros x. rewrite clauses_levels_spec.
    move=> [] cl. rewrite Clauses.union_spec.
    intros [[] incls]. apply H. apply clauses_levels_spec. exists cl. split => //.
    apply H0. apply clauses_levels_spec. exists cl; split => //.
  - exact H1.
  - eapply is_update_of_empty.
Qed.

(* To infer an extension, we weaken a valid model for V to a model for [V ∪ clauses_levels cls] by
   setting a minimal value for the new atoms in [clauses_levels cls \ V]
   such that the new clauses [cls] do not hold vacuously.
*)
(* Equations? infer_extension {V W init cls} (m : valid_model V W init cls) (cls' : clauses) :
  result (LevelSet.union (clauses_levels cls') V) LevelSet.empty (Clauses.union cls cls') (min_model m.(model_model) cls') :=
  infer_extension m cls' :=
    infer_model_extension (LevelSet.union (clauses_levels cls') V) (min_model m.(model_model) cls') cls cls' _.
Proof.
  repeat split.
  - pose proof (model_clauses_conclusions m). intros x. lsets.
  - pose proof (clauses_conclusions_levels cls'). lsets.
  - red. intros.
    unfold min_model. rewrite min_model_map_levels.
    pose proof (model_of_V m k).
    apply LevelSet.union_spec in H as []; auto.
Qed.

Definition enforce_clauses {V W init cls} (m : valid_model V W init cls) cls' : option model :=
  match infer_extension m cls' with
  | Loop _ _ _ => None
  | Model w m _ => Some m.(model_model)
  end.
*)
(* Definition enforce_clause {V W init cls} (m : valid_model V W init cls) cl : option model :=
  enforce_clauses m (Clauses.singleton cl). *)

Inductive constraint_type := UnivEq | UnivLe.

Notation constraint := (nonEmptyLevelExprSet * constraint_type * nonEmptyLevelExprSet)%type.

Definition enforce_constraint (cstr : constraint) (cls : clauses) : clauses :=
  let '(l, d, r) := cstr in
  match d with
  | UnivLe =>
    LevelExprSet.fold (fun lk acc => Clauses.add (r, lk) acc) l cls
  | UnivEq =>
    let cls :=
      LevelExprSet.fold (fun lk acc => Clauses.add (r, lk) acc) l cls
    in
    let cls' :=
      LevelExprSet.fold (fun rk acc => Clauses.add (l, rk) acc) r cls
    in cls'
  end.

Definition clauses_of_list := ClausesProp.of_list.
Definition list_of_clauses := Clauses.elements.
Definition valuation := LevelMap.t nat.

Definition premises_model_map (m : model) cls : model :=
  Clauses.fold (fun '(cl, concl) acc =>
    LevelExprSet.fold (fun '(l, k) acc =>
      add_max l k acc) cl acc) cls m.


Lemma premises_model_map_levels m cls k :
  LevelMap.In k (premises_model_map m cls) <->
    LevelSet.In k (clauses_premises_levels cls) \/ LevelMap.In k m.
Proof.
  rewrite /premises_model_map.
  rewrite clauses_premises_levels_spec.
  eapply ClausesProp.fold_rec.
  - intros s' he. intuition auto.
    destruct H0 as [cl []].
    clsets.
  - intros x a s' s'' inx ninx hadd ih.
    destruct x as [cl k'].
    rewrite In_fold_add_max ih.
    intuition auto.
    * left. exists (cl, k'); intuition auto.
      apply hadd. now left.
    * destruct H as [cl'' []]. left. exists cl''.
      intuition auto. apply hadd. now right.
    * destruct H3 as [cl'' []].
      apply hadd in H0 as []; subst.
      now left. right. now left.
Qed.


Variant checking_result (cls : clauses) (cl : clause) : Type :=
  | DoesNotHold : ~ entails cls cl -> checking_result cls cl
  | Entails : entails cls cl -> checking_result cls cl.

Definition zero_model levels : model :=
  LevelSet.fold (fun l acc => LevelMap.add l 0 acc) levels (LevelMap.empty _).

Definition premises_model V cl : LevelSet.t * model :=
  let levels := LevelSet.union (clause_levels cl) V in
  (levels, premises_model_map (zero_model levels) (Clauses.singleton cl)).

Program Definition loop_check {V init cls} (m : valid_model V V init cls) (cl : clause) : result (premises_model V cl).1 LevelSet.empty cls (premises_model V cl).2 :=
  loop (premises_model V cl).1 LevelSet.empty cls (premises_model V cl).2 (premises_model V cl).2 _.
Next Obligation.
  destruct m. split => //.
  - apply todo.
  - apply todo.
  - apply is_update_of_empty.
Qed.

Equations check {V init cls} (m : valid_model V V init cls) (cl : clause) : bool :=
  check m cl with loop_check m cl :=
    | Loop _ _ => false (* Actually impossible *)
    | Model W v _ =>
      let '(concl, k) := concl cl in
      match LevelMap.find concl v.(model_model) with
      | Some v => (k <=? v)
      | None => false
      end.


Equations? infer_model (cls : clauses) : option model :=
infer_model cls with loop (clauses_levels cls) LevelSet.empty cls (init_model cls) (init_model cls) _ :=
  | Loop _ _ => None
  | Model w vm heq => Some vm.(model_model).
Proof.
  split.
  - reflexivity.
  - apply infer_obligation_2.
  - apply is_update_of_empty.
Qed.

Definition enabled_clause (m : model) (cl : clause) :=
  exists z, min_premise m (premise cl) = Some z /\ (0 <= z)%Z.

Definition enabled_clauses (m : model) (cls : clauses) :=
  Clauses.For_all (enabled_clause m) cls.

Definition correct_model (cls : clauses) (m : model) :=
  enabled_clauses m cls /\ clauses_sem (valuation_of_model m) cls.

Definition infer_correctness cls := forall m, infer_model cls = Some m -> correct_model cls m.

Lemma enabled_clauses_ext m m' cls : m ⩽ m' -> enabled_clauses m cls -> enabled_clauses m' cls.
Proof. Admitted.

Lemma interp_prems_ge v (prems : nonEmptyLevelExprSet) :
  forall prem, LevelExprSet.In prem prems ->
  interp_expr v prem <= interp_prems v prems.
Proof.
  intros.
  unfold interp_prems.
  have he := to_nonempty_list_spec prems.
  destruct to_nonempty_list.
  pose proof to_nonempty_list_spec'.
  rewrite In_elements in H. rewrite -he in H. clear H0 he. clear -H.
  destruct H. subst t.
  - induction l. cbn. auto.
    cbn. lia.
  - induction l in H |- *.
    now cbn in H.
    cbn in H. destruct H; subst; cbn.
    * cbn. lia.
    * specialize (IHl H). lia.
Qed.

Lemma valid_clause_model model cl :
  enabled_clause model cl ->
  valid_clause model cl ->
  clause_sem (valuation_of_model model) cl.
Proof.
  unfold enabled_clause, valid_clause.
  destruct min_premise eqn:hmin => //= => //.
  2:{ intros [k' []]. congruence. }
  intros [k' [eq ge0]]. noconf eq.
  destruct cl as [prems [concl k]]; cbn.
  unfold level_value_above.
  elim: Z.ltb_spec => //= hz hrel. lia. cbn.
  destruct level_value eqn:hl => //.
  unfold interp_level. unfold level_value in hl. destruct LevelMap.find eqn:hfind => //. noconf hl.
  eapply LevelMap.find_2 in hfind.
  have conclm := valuation_of_model_spec _ _ _ hfind.
  set (v := (model_max _ - _)) in *.
  cbn in conclm.
  eapply LevelMap.find_1 in conclm. rewrite conclm.
  subst v.
  pose proof (@min_premise_spec model prems) as [premmin [prem [premin premeq]]].
  rewrite hmin in premeq.
  eapply Nat.le_trans. 2:{ eapply interp_prems_ge; tea. }
  unfold interp_expr. destruct prem as [prem k'].
  symmetry in premeq.
  move: premeq. unfold min_atom_value.
  unfold level_value. destruct (LevelMap.find prem) eqn:findp => //.
  intros [= <-].
  eapply LevelMap.find_2 in findp.
  have premm := valuation_of_model_spec _ _ _ findp.
  unfold interp_level.
  (* destruct premm as [vppos vpmap]. *)
  eapply LevelMap.find_1 in premm. rewrite premm.
  apply Nat.leb_le in hrel.
  assert (Z.to_nat (Z.of_nat n0 - Z.of_nat k') = n0 - k'). lia. rewrite H in hrel.
  assert (n0 - k' <= n - k). lia.
  have hm : n <= model_max model. eapply model_max_spec; tea.
  have hm' : n0 <= model_max model. eapply model_max_spec; tea.
  lia.
Qed.

Lemma infer_correct cls : infer_correctness cls.
Proof.
  intros m.
  funelim (infer_model cls) => //.
  intros [= <-]. clear Heq Heqcall. destruct vm as [model ofV isupd clsconcl ism]; cbn in *.
  set (V := clauses_levels cls) in *.
  assert (model_of V model).
  { intros l inl. eapply is_update_of_ext in isupd as mext. red in mext.
    (* eapply clauses_levels_spec in inl as [cl [hcl hin]]. *)
    unfold init_model in mext.
    have [kmin [hm incl]] := min_model_mapsto cls l inl.
    eapply mext in hm as [kmodel [mapmodel hmodel]].
    now exists kmodel. }
  unfold correct_model.
  have encl : enabled_clauses model cls.
  { eapply enabled_clauses_ext. apply is_update_of_ext in isupd. exact isupd.
    unfold enabled_clauses.
    intros x hin. unfold enabled_clause.
    pose proof (@min_premise_spec (init_model cls) (premise x)) as [premmin [prem [premin premeq]]].
    have inV : LevelSet.In prem (clauses_levels cls).
    { rewrite clauses_levels_spec. exists x; split => //. rewrite /clause_levels.
      eapply LevelSet.union_spec; left. rewrite levelexprset_levels_spec. exists prem.2.
      destruct prem. exact premin. }
    have [kmin [hm incl]] := min_model_mapsto cls prem inV.
    unfold init_model. rewrite premeq. unfold min_atom_value.
    destruct prem as [l k].
    eapply LevelMap.find_1 in hm. unfold level_value. rewrite hm. eexists; split; eauto.
    destruct incl as [cl [hin' [n [heq' [hin'' maxp]]]]]. subst n. red in maxp.
    eapply maxp in hin. eapply hin in premin. lia. }
  split => //.
  unfold clauses_sem.
  intros cl hin.
  eapply valid_clause_model. now eapply encl in hin.
  eapply Clauses.for_all_spec in ism; tc. now specialize (ism _ hin).
Qed.

(* If a clause checks, then it should be valid in any extension of the model *)
Lemma check_entails {V init cls} (m : valid_model V V init cls) (cl : clause) :
  check m cl = true -> forall m', model_model m ⩽ m' -> valid_clause m' cl.
Proof.
  funelim (check m cl) => //.
  destruct cl as [prems [concl k]]; unfold LoopChecking.concl, snd in *.
  destruct LevelMap.find as [conclval_v|] eqn:hfind => //.
  (* Found a value *)
  unfold valid_clause, level_value_above. cbn.
  move/Nat.leb_le => hgt.
  intros m' ext.
  destruct min_premise eqn:hmin => //.
  pose proof (min_premise_spec m' prems) as [minle mineq].
  unfold level_value.
  set (all_levels := clause_levels _ ∪ V) in *.
  set (undef_model := premises_model_map _ _) in *.
  have vcheck := model_ok v.
  unfold is_model in vcheck.
  assert (model_model v ⩽ model_model m). admit.
  assert (model_model v ⩽ m'). etransitivity; tea.
  eapply LevelMap.find_2 in hfind.
  apply H0 in hfind as [k' [hmk' neq]]. red in neq. rename k' into conclval_m'.
  eapply LevelMap.find_1 in hmk'. rewrite hmk'.
Abort.
  (*eapply Z.leb_le. transitivity conclval_v => //.
  destruct (Z.leb_spec z 0).
  (* If min_premise m' z > 0 in the final model, it means prems -> prems + 1,
    i.e. there is a loop, which is impossible.
    We start with min_premise undef_model prems = Some 0 by definition.
    Any increase of [z]'s value means a consequence of [z]
    was found requiring to increase its value. But then it must mean [z -> z + 1].
  *)
  exfalso.
  have updundef := model_updates v.
  have me := is_update_of_ext updundef.
  assert (not (exists x, is_loop cls x)). admit.
  apply H3.
  destruct mineq as [minelt [hprems hmin']].
  exists (singleton minelt).
  unfold is_loop, to_clauses.
  intros x hin.
  rewrite LevelExprSet.fold_spec in hin.
  move: hin.
  assert (LevelExprSet.elements (succ_prems (singleton minelt)) = [succ_expr minelt]). admit.
  rewrite H4 //=. unfold flip. move/Clauses.add_spec. intros [->|] => //. 2:{ now apply Clauses.empty_spec in H5. }
  destruct minelt as [min k']. cbn.

Abort.
*)

End LoopChecking.
