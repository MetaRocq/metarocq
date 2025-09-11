From Stdlib Require Import OrdersAlt MSetList MSetAVL MSetFacts MSetProperties MSetDecide FMapAVL.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils MRMSets MRFSets.
From MetaRocq.Common Require Import BasicAst config.
From Stdlib Require Import ssreflect.

Local Open Scope nat_scope.
Local Open Scope string_scope2.

Implicit Types (cf : checker_flags).

Ltac absurd :=
  match goal with
  | [H: ~ True |- _] => elim (H I)
  | [H : False |- _] => elim H
  | H: is_true false |- _ => discriminate H
  | |- False -> _ => let H := fresh in intro H; elim H
  | |- _ -> False -> _ => let H := fresh in intros ? H; elim H
  | |- is_true false -> _ => let H := fresh in intro H; discriminate H
  | |- _ -> is_true false -> _ => let H := fresh in intros ? H; discriminate H
  end.
#[global]
Hint Extern 10 => absurd : core.

(** * Valuations *)

(** A valuation is a universe level (nat) given for each
    universe lvariable (Level.t).
    It is >= for polymorphic concrete_sort and > 0 for monomorphic concrete_sort. *)
Record valuation :=
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.

Class Evaluable (A : Type) := val : valuation -> A -> nat.


(** Levels are Set or Level or lvar *)
Module Level.
  Inductive t_ : Set :=
  | lzero
  | level (_ : string)
  | lvar (_ : nat) (* these are debruijn indices *).
  Derive NoConfusion for t_.

  Definition t := t_.

  Definition is_set (x : t) :=
    match x with
    | lzero => true
    | _ => false
    end.

  Definition is_var (l : t) :=
    match l with
    | lvar _ => true
    | _ => false
    end.

  Global Instance Evaluable : Evaluable t
    := fun v l => match l with
               | lzero =>  (0%nat)
               | level s => (Pos.to_nat (v.(valuation_mono) s))
               | lvar x => (v.(valuation_poly) x)
               end.


  Definition compare (l1 l2 : t) : comparison :=
    match l1, l2 with
    | lzero, lzero => Eq
    | lzero, _ => Lt
    | _, lzero => Gt
    | level s1, level s2 => string_compare s1 s2
    | level _, _ => Lt
    | _, level _ => Gt
    | lvar n, lvar m => Nat.compare n m
    end.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | ltSetLevel s : lt_ lzero (level s)
  | ltSetlvar n : lt_ lzero (lvar n)
  | ltLevelLevel s s' : StringOT.lt s s' -> lt_ (level s) (level s')
  | ltLevellvar s n : lt_ (level s) (lvar n)
  | ltlvarlvar n n' : Nat.lt n n' -> lt_ (lvar n) (lvar n').
  Derive Signature for lt_.

  Definition lt := lt_.

  Definition lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros [| |] X; inversion X.
      now eapply irreflexivity in H1.
      eapply Nat.lt_irrefl; tea.
    - intros [| |] [| |] [| |] X1 X2;
        inversion X1; inversion X2; constructor.
      now transitivity s0.
      etransitivity; tea.
  Qed.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros x y e z t e'. unfold eq in *; subst. reflexivity.
  Qed.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [] []; repeat constructor.
    - eapply CompareSpec_Proper.
      5: eapply CompareSpec_string. 4: reflexivity.
      all: split; [now inversion 1|]. now intros ->.
      all: intro; now constructor.
    - eapply CompareSpec_Proper.
      5: eapply Nat.compare_spec. 4: reflexivity.
      all: split; [now inversion 1|]. now intros ->.
      all: intro; now constructor.
  Qed.

  Definition eq_level l1 l2 :=
    match l1, l2 with
    | Level.lzero, Level.lzero => true
    | Level.level     s1, Level.level     s2 => ReflectEq.eqb s1 s2
    | Level.lvar n1, Level.lvar n2 => ReflectEq.eqb n1 n2
    | _, _ => false
    end.

  #[global, program] Instance reflect_level : ReflectEq Level.t := {
    eqb := eq_level
  }.
  Next Obligation.
    destruct x, y.
    all: unfold eq_level.
    all: try solve [ constructor ; reflexivity ].
    all: try solve [ constructor ; discriminate ].
    - destruct (ReflectEq.eqb_spec t0 t1) ; nodec.
      constructor. f_equal. assumption.
    - destruct (ReflectEq.eqb_spec n n0) ; nodec.
      constructor. subst. reflexivity.
  Defined.

  Global Instance eqb_refl : @Reflexive Level.t eqb.
  Proof.
    intros x. apply ReflectEq.eqb_refl.
  Qed.

  Definition eqb := eq_level.

  Lemma eqb_spec l l' : reflect (eq l l') (eqb l l').
  Proof.
    apply reflectProp_reflect.
    now generalize (eqb_spec l l').
  Qed.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

  Definition eq_dec : forall (l1 l2 : t), {l1 = l2}+{l1 <> l2} := Classes.eq_dec.

  #[refine] Instance reflect_eq : ReflectEq t :=
    { ReflectEq.eqb := eqb }.
  Proof.
    intros x y. apply reflect_reflectProp, eqb_spec.
  Qed.

End Level.

Module LevelSet := MSetAVL.Make Level.
Module LevelSetFact := WFactsOn Level LevelSet.
Module LevelSetOrdProp := MSetProperties.OrdProperties LevelSet.
Module LevelSetProp := LevelSetOrdProp.P.
Module LevelSetDecide := LevelSetProp.Dec.
Module LevelSetExtraOrdProp := MSets.ExtraOrdProperties LevelSet LevelSetOrdProp.
Module LevelSetExtraDecide := MSetAVL.Decide Level LevelSet.
Module LS := LevelSet.

Ltac lsets := LevelSetDecide.fsetdec.
Notation "(=_lset)" := LevelSet.Equal (at level 0).
Infix "=_lset" := LevelSet.Equal (at level 30).
Notation "(==_lset)" := LevelSet.equal (at level 0).
Infix "==_lset" := LevelSet.equal (at level 30).

Section LevelSetMoreFacts.

  Definition LevelSet_pair x y
    := LevelSet.add y (LevelSet.singleton x).

  Lemma LevelSet_pair_In x y z :
    LevelSet.In x (LevelSet_pair y z) -> x = y \/ x = z.
  Proof.
    intro H. apply LevelSetFact.add_iff in H.
    destruct H; [intuition|].
    apply LevelSetFact.singleton_1 in H; intuition.
  Qed.

  Definition LevelSet_mem_union (s s' : LevelSet.t) x :
    LevelSet.mem x (LevelSet.union s s') <-> LevelSet.mem x s \/ LevelSet.mem x s'.
  Proof.
    rewrite LevelSetFact.union_b.
    apply orb_true_iff.
  Qed.

  Lemma LevelSet_In_fold_right_add x l :
    In x l <-> LevelSet.In x (fold_right LevelSet.add LevelSet.empty l).
  Proof.
    split.
    - induction l; simpl => //.
      intros [<-|H].
      * eapply LevelSet.add_spec; left; auto.
      * eapply LevelSet.add_spec; right; auto.
    - induction l; simpl => //.
      * now rewrite LevelSetFact.empty_iff.
      * rewrite LevelSet.add_spec. intuition auto.
  Qed.

  Lemma LevelSet_union_empty s : LevelSet.Equal (LevelSet.union LevelSet.empty s) s.
  Proof.
    intros x; rewrite LevelSet.union_spec. lsets.
  Qed.
End LevelSetMoreFacts.

(* prop level is Prop or SProp *)
Module PropLevel.

  Inductive t := lSProp | lProp.
  Derive NoConfusion EqDec for t.
  (* Global Instance PropLevel_Evaluable : Evaluable t :=
    fun v l => match l with
              lSProp => -1
            | lProp => -1
            end. *)

  Definition compare (l1 l2 : t) : comparison :=
    match l1, l2 with
    | lSProp, lSProp  => Eq
    | lProp, lProp  => Eq
    | lProp, lSProp => Gt
    | lSProp, lProp => Lt
    end.

  Inductive lt_ : t -> t -> Prop :=
    ltSPropProp : lt_ lSProp lProp.

  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
  split.
  - intros n X. destruct n;inversion X.
  - intros n1 n2 n3 X1 X2. destruct n1,n2,n3;auto; try inversion X1;try inversion X2.
  Defined.

End PropLevel.

Module LevelExpr.
  Definition t := (Level.t * nat)%type.

  Global Instance Evaluable : Evaluable t
    := fun v l => (snd l + val v (fst l)).

  Definition succ (l : t) : t := (fst l, S (snd l)).

  Definition add (k : nat) (l : t) : t := (fst l, k + snd l).

  Definition get_level (e : t) : Level.t := fst e.

  Definition get_noprop (e : LevelExpr.t) := Some (fst e).

  Definition is_level (e : t) : bool :=
    match e with
    | (_, 0%nat) => true
    | _  => false
    end.

  Definition make (l : Level.t) : t := (l, 0%nat).

  Definition set : t := (Level.lzero, 0%nat).
  Definition type1 : t := (Level.lzero, 1%nat).

  Definition eq : t -> t -> Prop := eq.

  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | ltLevelExpr1 l n n' : (n < n')%nat -> lt_ (l, n) (l, n')
  | ltLevelExpr2 l l' b b' : Level.lt l l' -> lt_ (l, b) (l', b').
  Derive Signature for lt_.
  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros x X; inversion X. subst. lia. subst.
      eapply Level.lt_strorder; eassumption.
    - intros x y z X1 X2; invs X1; invs X2; constructor; tea.
      etransitivity; tea.
      etransitivity; tea.
  Qed.

  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
    intros x x' H1 y y' H2; now rewrite H1 H2.
  Qed.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | (l1, b1), (l2, b2) =>
      match Level.compare l1 l2 with
      | Eq => Nat.compare b1 b2
      | x => x
      end
    end.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [? ?] [? ?]; cbn; repeat constructor.
    destruct (Level.compare_spec t0 t1); repeat constructor; tas.
    subst.
    destruct (Nat.compare_spec n n0); repeat constructor; tas. congruence.
  Qed.

  Global Instance reflect_t : ReflectEq t := reflect_prod _ _ .

  Definition eq_dec : forall (l1 l2 : t), {l1 = l2} + {l1 <> l2} := Classes.eq_dec.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

  Lemma val_make v l
    : val v (LevelExpr.make l) = val v l.
  Proof.
    destruct l eqn:H; cbnr.
  Qed.

  Lemma val_make_npl v (l : Level.t)
    : val v (LevelExpr.make l) = val v l.
  Proof.
    destruct l; cbnr.
  Qed.

End LevelExpr.

Module LevelExprSet.
  Include MSetList.MakeWithLeibniz LevelExpr.

  Definition levels (e : t) :=
    fold (fun le => LevelSet.add (LevelExpr.get_level le)) e LevelSet.empty.

  Record nonEmptyLevelExprSet
    := { t_set : LevelExprSet.t ;
         t_ne  : LevelExprSet.is_empty t_set = false }.
End LevelExprSet.

Module LevelExprSetFact := WFactsOn LevelExpr LevelExprSet.
Module LevelExprSetOrdProp := MSetProperties.OrdProperties LevelExprSet.
Module LevelExprSetProp := LevelExprSetOrdProp.P.
Module LevelExprSetDecide := LevelExprSetProp.Dec.
Module LevelExprSetExtraOrdProp := MSets.ExtraOrdProperties LevelExprSet LevelExprSetOrdProp.

(* We have decidable equality w.r.t leibniz equality for sets of levels.
  This means concrete_sort also has a decidable equality. *)
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

Import LevelExprSet (nonEmptyLevelExprSet, t_set, t_ne).

Derive NoConfusion for nonEmptyLevelExprSet.

(** This coercion allows to see the non-empty set as a regular [LevelExprSet.t] *)
Coercion t_set : nonEmptyLevelExprSet >-> LevelExprSet.t.

Module NonEmptySetFacts.
  Definition singleton (e : LevelExpr.t) : nonEmptyLevelExprSet
    := {| t_set := LevelExprSet.singleton e;
          t_ne := eq_refl |}.

  Lemma not_Empty_is_empty s :
    ~ LevelExprSet.Empty s -> LevelExprSet.is_empty s = false.
  Proof.
    intro H. apply not_true_is_false. intro H'.
    apply H. now apply LevelExprSetFact.is_empty_2 in H'.
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

  Program Definition to_nonempty_list (u : nonEmptyLevelExprSet) : LevelExpr.t * list LevelExpr.t
    := match LevelExprSet.elements u with
       | [] => False_rect _ _
       | e :: l => (e, l)
       end.
  Next Obligation.
    destruct u as [u1 u2]; cbn in *. revert u2.
    apply eq_true_false_abs.
    unfold LevelExprSet.is_empty, LevelExprSet.Raw.is_empty,
    LevelExprSet.elements, LevelExprSet.Raw.elements in *.
    rewrite <- Heq_anonymous; reflexivity.
  Qed.

  Lemma singleton_to_nonempty_list e : to_nonempty_list (singleton e) = (e, []).
  Proof. reflexivity. Defined.

  Lemma to_nonempty_list_spec u :
    let '(e, u') := to_nonempty_list u in
    e :: u' = LevelExprSet.elements u.
  Proof.
    destruct u as [u1 u2].
    unfold to_nonempty_list; cbn.
    set (l := LevelExprSet.elements u1). unfold l at 2 3 4.
    set (e := (eq_refl: l = LevelExprSet.elements u1)); clearbody e.
    destruct l.
    - exfalso. revert u2. apply eq_true_false_abs.
      unfold LevelExprSet.is_empty, LevelExprSet.Raw.is_empty,
      LevelExprSet.elements, LevelExprSet.Raw.elements in *.
      rewrite <- e; reflexivity.
    - reflexivity.
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

  Lemma elements_not_empty (u : nonEmptyLevelExprSet) : LevelExprSet.elements u <> [].
  Proof.
    destruct u as [u1 u2]; cbn; intro e.
    unfold LevelExprSet.is_empty, LevelExprSet.elements,
    LevelExprSet.Raw.elements in *.
    rewrite e in u2; discriminate.
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
    destruct u1 as [u1 u2], v1 as [v1 v2]; cbn in *.
    destruct H. now rewrite (uip_bool _ _ u2 v2).
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


End NonEmptySetFacts.
Import NonEmptySetFacts.


Module Universe.
  (** A universe / an algebraic expression is a list of universe expressions which is:
        - sorted
        - without duplicate
        - non empty *)

  Definition t := nonEmptyLevelExprSet.

  (* We use uip on the is_empty condition *)
  #[global, program] Instance levelexprset_reflect : ReflectEq t :=
    { eqb x y := eqb x.(t_set) y.(t_set) }.
  Next Obligation.
    destruct (eqb_spec (t_set x) (t_set y)); constructor.
    destruct x, y; cbn in *. subst.
    now rewrite (uip t_ne0 t_ne1).
    intros e; subst x; apply H.
    reflexivity.
  Qed.

  #[global] Instance eq_dec_univ0 : EqDec t := eq_dec.

  Definition make (e: LevelExpr.t) : t := singleton e.
  Definition make' (l: Level.t) : t := singleton (LevelExpr.make l).

  Lemma make'_inj l l' : make' l = make' l' -> l = l'.
  Proof.
    destruct l, l' => //=; now inversion 1.
  Qed.

  (** The non empty / sorted / without dup list of univ expressions, the
    components of the pair are the head and the tail of the (non empty) list *)
  Definition exprs : t -> LevelExpr.t * list LevelExpr.t := to_nonempty_list.

  Global Instance Evaluable : Evaluable Universe.t
    := fun v u =>
      let '(e, u) := Universe.exprs u in
      List.fold_left (fun n e => Nat.max (val v e) n) u (val v e).

  (** Test if the universe is a lub of levels or contains +n's. *)
  Definition is_levels (u : t) : bool :=
    LevelExprSet.for_all LevelExpr.is_level u.

  (** Test if the universe is a level or an algebraic universe. *)
  Definition is_level (u : t) : bool :=
    (LevelExprSet.cardinal u =? 1)%nat && is_levels u.

  Definition succ : t -> t := map LevelExpr.succ.

  Definition add (k : nat) : t -> t := map (LevelExpr.add k).

  Definition from_kernel_repr (e : Level.t * nat) (es : list (Level.t * nat)) : t
    := add_list es (Universe.make e).

  (** The l.u.b. of 2 non-prop universe sets *)
  Definition sup : t -> t -> t := non_empty_union.

  Definition get_is_level (u : t) : option Level.t :=
    match LevelExprSet.elements u with
    | [(l, 0%nat)] => Some l
    | _ => None
    end.

  Lemma val_make v e : val v (make e) = val v e.
  Proof. reflexivity. Qed.

  Lemma val_make' v l
    : val v (make' l) = val v l.
  Proof. reflexivity. Qed.

  Definition lt : t -> t -> Prop := LevelExprSet.lt.
  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. repeat intro; subst; reflexivity. Qed.
  #[global] Instance lt_strorder : StrictOrder lt.
  Proof.
    cbv [lt]; constructor.
    { intros ? H. apply irreflexivity in H; assumption. }
    { intros ??? H1 H2; etransitivity; tea. }
  Qed.



End Universe.

Ltac u :=
  change LevelSet.elt with Level.t in *;
  change LevelExprSet.elt with LevelExpr.t in *.
  (* change ConstraintSet.elt with UnivConstraint.t in *. *)


Lemma val_fold_right (u : Universe.t) v :
  val v u = fold_right (fun e x => Nat.max (val v e) x) (val v (Universe.exprs u).1)
                       (List.rev (Universe.exprs u).2).
Proof.
  unfold val at 1, Universe.Evaluable.
  destruct (Universe.exprs u).
  now rewrite fold_left_rev_right.
Qed.

Lemma val_In_le (u : Universe.t) v e :
  LevelExprSet.In e u -> val v e <= val v u.
Proof.
  intro H. rewrite val_fold_right.
  apply In_to_nonempty_list_rev in H.
  fold Universe.exprs in H; destruct (Universe.exprs u); cbn in *.
  destruct H as [H|H].
  - subst. induction (List.rev l); cbnr. lia.
  - induction (List.rev l); cbn; invs H.
    + u; lia.
    + specialize (IHl0 H0). lia.
Qed.

Lemma val_In_max (u : Universe.t) v :
  exists e, LevelExprSet.In e u /\ val v e = val v u.
Proof.
  eapply iff_ex. {
    intro. eapply and_iff_compat_r. apply In_to_nonempty_list_rev. }
  rewrite val_fold_right. fold Universe.exprs; destruct (Universe.exprs u) as [e l]; cbn in *.
  clear. induction (List.rev l); cbn.
  - exists e. split; cbnr. left; reflexivity.
  - destruct IHl0 as [e' [H1 H2]].
    destruct (Nat.max_dec (val v a) (fold_right (fun e0 x0 => Nat.max (val v e0) x0)
                                               (val v e) l0)) as [H|H];
      rewrite H; clear H.
    + exists a. split; cbnr. right. now constructor.
    + rewrite <- H2. exists e'. split; cbnr.
      destruct H1 as [H1|H1]; [now left|right]. now constructor 2.
Qed.

Lemma val_ge_caract (u : Universe.t) v k :
  (forall e, LevelExprSet.In e u -> val v e <= k) <-> val v u <= k.
Proof.
  split.
  - eapply imp_iff_compat_r. {
      eapply iff_forall; intro. eapply imp_iff_compat_r.
      apply In_to_nonempty_list_rev. }
    rewrite val_fold_right.
    fold Universe.exprs; destruct (Universe.exprs u) as [e l]; cbn; clear.
    induction (List.rev l); cbn.
    + intros H. apply H. left; reflexivity.
    + intros H.
      destruct (Nat.max_dec (val v a) (fold_right (fun e0 x => Nat.max (val v e0) x)
                                                 (val v e) l0)) as [H'|H'];
        rewrite H'; clear H'.
      * apply H. right. now constructor.
      * apply IHl0. intros x [H0|H0]; apply H. now left.
        right; now constructor 2.
  - intros H e He. eapply val_In_le in He. etransitivity; eassumption.
Qed.

Lemma val_le_caract (u : Universe.t) v k :
  (exists e, LevelExprSet.In e u /\ k <= val v e) <-> k <= val v u.
Proof.
  split.
  - eapply imp_iff_compat_r. {
      eapply iff_ex; intro. eapply and_iff_compat_r. apply In_to_nonempty_list_rev. }
    rewrite val_fold_right.
    fold Universe.exprs; destruct (Universe.exprs u) as [e l]; cbn; clear.
    induction (List.rev l); cbn.
    + intros H. destruct H as [e' [[H1|H1] H2]].
      * now subst.
      * invs H1.
    + intros [e' [[H1|H1] H2]].
      * forward IHl0; [|lia]. exists e'. split; tas. left; assumption.
      * invs H1.
        -- u; lia.
        -- forward IHl0; [|lia]. exists e'. split; tas. right; assumption.
  - intros H. destruct (val_In_max u v) as [e [H1 H2]].
    exists e. rewrite H2; split; assumption.
Qed.



Lemma val_caract (u : Universe.t) v k :
  val v u = k
  <-> (forall e, LevelExprSet.In e u -> val v e <= k)
    /\ exists e, LevelExprSet.In e u /\ val v e = k.
Proof.
  split.
  - intros <-; split.
    + apply val_In_le.
    + apply val_In_max.
  - intros [H1 H2].
    apply val_ge_caract in H1.
    assert (k <= val v u); [clear H1|lia].
    apply val_le_caract. destruct H2 as [e [H2 H2']].
    exists e. split; tas. lia.
Qed.

Lemma val_add v e (s: Universe.t)
  : val v (add e s) = Nat.max (val v e) (val v s).
Proof.
  apply val_caract. split.
  - intros e' H. apply LevelExprSet.add_spec in H. destruct H as [H|H].
    + subst. u; lia.
    + eapply val_In_le with (v:=v) in H. lia.
  - destruct (Nat.max_dec (val v e) (val v s)) as [H|H]; rewrite H; clear H.
    + exists e. split; cbnr. apply LevelExprSetFact.add_1. reflexivity.
    + destruct (val_In_max s v) as [e' [H1 H2]].
      exists e'. split; tas. now apply LevelExprSetFact.add_2.
Qed.

Lemma val_sup v s1 s2 :
  val v (Universe.sup s1 s2) = Nat.max (val v s1) (val v s2).
Proof.
  eapply val_caract. cbn. split.
  - intros e' H. eapply LevelExprSet.union_spec in H. destruct H as [H|H].
    + eapply val_In_le with (v:=v) in H. lia.
    + eapply val_In_le with (v:=v) in H. lia.
  - destruct (Nat.max_dec (val v s1) (val v s2)) as [H|H]; rewrite H; clear H.
    + destruct (val_In_max s1 v) as [e' [H1 H2]].
      exists e'. split; tas. apply LevelExprSet.union_spec. now left.
    + destruct (val_In_max s2 v) as [e' [H1 H2]].
      exists e'. split; tas. apply LevelExprSet.union_spec. now right.
Qed.

Ltac proper := let H := fresh in try (intros ? ? H; destruct H; reflexivity).

Lemma for_all_elements (P : LevelExpr.t -> bool) u :
  LevelExprSet.for_all P u = forallb P (LevelExprSet.elements u).
Proof.
  apply LevelExprSetFact.for_all_b; proper.
Qed.


Lemma universe_get_is_level_correct u l :
  Universe.get_is_level u = Some l -> u = Universe.make' l.
Proof.
  intro H.
  unfold Universe.get_is_level in *.
  destruct (LevelExprSet.elements u) as [|l0 L] eqn:Hu1; [discriminate |].
  destruct l0, L; try discriminate.
  * destruct n; inversion H; subst.
    apply eq_univ''; apply Hu1.
  * destruct n; discriminate.
Qed.


Lemma sup0_comm x1 x2 :
  Universe.sup x1 x2 = Universe.sup x2 x1.
Proof.
  apply eq_univ'; simpl. unfold LevelExprSet.Equal.
  intros H. rewrite !LevelExprSet.union_spec. intuition.
Qed.

(*
Lemma val_zero_exprs v (l : Universe.t) : 0 <= val v l.
Proof.
  rewrite val_fold_right.
  destruct (Universe.exprs l) as [e u']; clear l; cbn.
  induction (List.rev u'); simpl.
  - destruct e as [npl_expr].
    destruct npl_expr as [t b].
    cbn.
    assert (0 <= val v t) by apply Level.val_zero.
    destruct b;lia.
  - pose proof (LevelExpr.val_zero a v); lia.
Qed. *)


Module ConstraintType.
  Inductive t_ : Set := Le (z : Z) | Eq.
  Derive NoConfusion EqDec for t_.

  Definition t := t_.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition Le0 := Le 0.
  Definition Lt := Le 1.

  Inductive lt_ : t -> t -> Prop :=
  | LeLe n m : (n < m)%Z -> lt_ (Le n) (Le m)
  | LeEq n : lt_ (Le n) Eq.
  Derive Signature for lt_.
  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; intro X; inversion X. lia.
    - intros ? ? ? X Y; invs X; invs Y; constructor. lia.
  Qed.

  Global Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros ? ? X ? ? Y; invs X; invs Y. reflexivity.
  Qed.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | Le n, Le m => Z.compare n m
    | Le _, Eq => Datatypes.Lt
    | Eq, Eq => Datatypes.Eq
    | Eq, _  => Datatypes.Gt
    end.

  Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x, y; repeat constructor. simpl.
    destruct (Z.compare_spec z z0); simpl; constructor.
    subst; constructor. now constructor. now constructor.
  Qed.

  Lemma eq_dec x y : {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. decide equality. apply Z.eq_dec.
  Qed.
End ConstraintType.

Module UnivConstraint.
  Definition t : Type := Universe.t * ConstraintType.t * Universe.t.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition make l1 ct l2 : t := (l1, ct, l2).

  Inductive lt_ : t -> t -> Prop :=
  | lt_Level2 l1 t (l2 l2' : Universe.t) : LevelExprSet.lt l2 l2' -> lt_ (l1, t, l2) (l1, t, l2')
  | lt_Cstr l1 t t' l2 l2' : ConstraintType.lt t t' -> lt_ (l1, t, l2) (l1, t', l2')
  | lt_Level1 (l1 l1' : Universe.t) t t' l2 l2' : LevelExprSet.lt l1 l1' -> lt_ (l1, t, l2) (l1', t', l2').
  Derive Signature for lt_.
  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; intro X; inversion X; subst;
        try (eapply LevelExprSet.lt_strorder; eassumption).
      eapply ConstraintType.lt_strorder; eassumption.
    - intros ? ? ? X Y; invs X; invs Y; constructor; tea.
      etransitivity; eassumption.
      2: etransitivity; eassumption.
      eapply ConstraintType.lt_strorder; eassumption.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros ? ? X ? ? Y; invs X; invs Y. reflexivity.
  Qed.

  Definition compare : t -> t -> comparison :=
    fun '(l1, t, l2) '(l1', t', l2') =>
      compare_cont (LevelExprSet.compare l1 l1')
        (compare_cont (ConstraintType.compare t t')
                    (LevelExprSet.compare l2 l2')).

  Lemma universe_eq (x y : Universe.t) : t_set x = t_set y -> x = y.
  Proof.
    destruct x, y; cbn. intros ->.
    now eapply NonEmptySetFacts.eq_univ; cbn.
  Qed.

  Lemma compare_spec x y
    : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x as [[l1 t] l2], y as [[l1' t'] l2']; cbn.
    destruct (LevelExprSet.compare_spec l1 l1'); cbn; repeat constructor; tas.
    eapply LevelExprSet.eq_leibniz, universe_eq in H. subst l1'.
    destruct (ConstraintType.compare_spec t t'); cbn; repeat constructor; tas.
    invs H.
    destruct (LevelExprSet.compare_spec l2 l2'); cbn; repeat constructor; tas.
    eapply LevelExprSet.eq_leibniz, universe_eq in H. now subst l2'.
  Qed.

  Lemma eq_dec x y : {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. decide equality; apply eq_dec.
  Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.
End UnivConstraint.

Module UnivConstraintSet := MSetAVL.Make UnivConstraint.
Module UnivConstraintSetFact := WFactsOn UnivConstraint UnivConstraintSet.
Module UnivConstraintSetOrdProp := MSetProperties.OrdProperties UnivConstraintSet.
Module UnivConstraintSetProp := UnivConstraintSetOrdProp.P.
(* Module CS := UnivConstraintSet. *)
Module UnivConstraintSetDecide := UnivConstraintSetProp.Dec.
Module UnivConstraintSetExtraOrdProp := MSets.ExtraOrdProperties UnivConstraintSet UnivConstraintSetOrdProp.
Module UnivConstraintSetExtraDecide := MSetAVL.Decide UnivConstraint UnivConstraintSet.
(* Ltac csets := UnivConstraintSetDecide.fsetdec. *)
Ltac ucsets := UnivConstraintSetDecide.fsetdec.

Module LevelConstraint.
  Definition t : Set := Level.t * ConstraintType.t * Level.t.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition make l1 ct l2 : t := (l1, ct, l2).

  Inductive lt_ : t -> t -> Prop :=
  | lt_Level2 l1 t l2 l2' : Level.lt l2 l2' -> lt_ (l1, t, l2) (l1, t, l2')
  | lt_Cstr l1 t t' l2 l2' : ConstraintType.lt t t' -> lt_ (l1, t, l2) (l1, t', l2')
  | lt_Level1 l1 l1' t t' l2 l2' : Level.lt l1 l1' -> lt_ (l1, t, l2) (l1', t', l2').
  Derive Signature for lt_.
  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; intro X; inversion X; subst;
        try (eapply Level.lt_strorder; eassumption).
      eapply ConstraintType.lt_strorder; eassumption.
    - intros ? ? ? X Y; invs X; invs Y; constructor; tea.
      etransitivity; eassumption.
      2: etransitivity; eassumption.
      eapply ConstraintType.lt_strorder; eassumption.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros ? ? X ? ? Y; invs X; invs Y. reflexivity.
  Qed.

  Definition compare : t -> t -> comparison :=
    fun '(l1, t, l2) '(l1', t', l2') =>
      compare_cont (Level.compare l1 l1')
        (compare_cont (ConstraintType.compare t t')
                    (Level.compare l2 l2')).

  Lemma compare_spec x y
    : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x as [[l1 t] l2], y as [[l1' t'] l2']; cbn.
    destruct (Level.compare_spec l1 l1'); cbn; repeat constructor; tas.
    invs H.
    destruct (ConstraintType.compare_spec t t'); cbn; repeat constructor; tas.
    invs H.
    destruct (Level.compare_spec l2 l2'); cbn; repeat constructor; tas.
    invs H. reflexivity.
  Qed.

  Lemma eq_dec x y : {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. decide equality; apply eq_dec.
  Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.
End LevelConstraint.

Module ConstraintSet := MSetAVL.Make LevelConstraint.
Module ConstraintSetFact := WFactsOn LevelConstraint ConstraintSet.
Module ConstraintSetProp := WPropertiesOn LevelConstraint ConstraintSet.
Module CS := ConstraintSet.
Module ConstraintSetDecide := WDecide (ConstraintSet).
Ltac csets := ConstraintSetDecide.fsetdec.

Notation "(=_cset)" := ConstraintSet.Equal (at level 0).
Infix "=_cset" := ConstraintSet.Equal (at level 30).
Notation "(==_cset)" := ConstraintSet.equal (at level 0).
Infix "==_cset" := ConstraintSet.equal (at level 30).

Definition declared_cstr_levels levels (cstr : LevelConstraint.t) :=
  let '(l1,_,l2) := cstr in
  LevelSet.In l1 levels /\ LevelSet.In l2 levels.

Definition is_declared_cstr_levels levels (cstr : LevelConstraint.t) : bool :=
  let '(l1,_,l2) := cstr in
  LevelSet.mem l1 levels && LevelSet.mem l2 levels.

Definition declared_univ_cstr_levels levels (cstr : UnivConstraint.t) :=
  let '(l1,_,l2) := cstr in
  LevelSet.Subset (LevelExprSet.levels l1) levels /\ LevelSet.Subset (LevelExprSet.levels l2) levels.

Definition is_declared_univ_cstr_levels levels (cstr : UnivConstraint.t) : bool :=
  let '(l1,_,l2) := cstr in
  LevelSet.subset (LevelExprSet.levels l1) levels && LevelSet.subset (LevelExprSet.levels l2) levels.

Lemma CS_union_empty s : ConstraintSet.union ConstraintSet.empty s =_cset s.
Proof.
  intros x; rewrite ConstraintSet.union_spec. lsets.
Qed.

Lemma CS_For_all_union f cst cst' : ConstraintSet.For_all f (ConstraintSet.union cst cst') ->
  ConstraintSet.For_all f cst.
Proof.
  unfold CS.For_all.
  intros IH x inx. apply (IH x).
  now eapply CS.union_spec; left.
Qed.

Lemma CS_For_all_add P x s : CS.For_all P (CS.add x s) -> P x /\ CS.For_all P s.
Proof.
  intros.
  split.
  * apply (H x), CS.add_spec; left => //.
  * intros y iny. apply (H y), CS.add_spec; right => //.
Qed.

#[global] Instance CS_For_all_proper P : Morphisms.Proper ((=_cset) ==> iff)%signature (ConstraintSet.For_all P).
Proof.
  intros s s' eqs.
  unfold CS.For_all. split; intros IH x inxs; apply (IH x);
  now apply eqs.
Qed.

(** {6 Sort instances} *)

Module Instance.

  (** A universe instance represents a vector of argument concrete_sort
      to a polymorphic definition (constant, inductive or constructor). *)
  Definition t : Set := list Level.t.

  Definition empty : t := [].
  Definition is_empty (i : t) : bool :=
    match i with
    | [] => true
    | _ => false
    end.

  Definition eqb (i j : t) :=
    forallb2 Level.eqb i j.

  Definition equal_upto (f : Level.t -> Level.t -> bool) (i j : t) :=
    forallb2 f i j.
End Instance.

Module UContext.
  Definition t := list name × (Instance.t × ConstraintSet.t).

  Definition make' : Instance.t -> ConstraintSet.t -> Instance.t × ConstraintSet.t := pair.
  Definition make (ids : list name) (inst_ctrs : Instance.t × ConstraintSet.t) : t := (ids, inst_ctrs).

  Definition empty : t := ([], (Instance.empty, ConstraintSet.empty)).

  Definition instance : t -> Instance.t := fun x => fst (snd x).
  Definition constraints : t -> ConstraintSet.t := fun x => snd (snd x).

  Definition dest : t -> list name * (Instance.t * ConstraintSet.t) := fun x => x.
End UContext.

Module AUContext.
  Definition t := list name × ConstraintSet.t.

  Definition make (ids : list name) (ctrs : ConstraintSet.t) : t := (ids, ctrs).
  Definition repr (x : t) : UContext.t :=
    let (u, cst) := x in
    (u, (mapi (fun i _ => Level.lvar i) u, cst)).

  Definition levels (uctx : t) : LevelSet.t :=
    LevelSetProp.of_list (fst (snd (repr uctx))).

  #[local]
  Existing Instance EqDec_ReflectEq.
  Definition inter (au av : AUContext.t) : AUContext.t :=
    let prefix := (split_prefix au.1 av.1).1.1 in
    let lvls := fold_left_i (fun s i _ => LevelSet.add (Level.lvar i) s) prefix LevelSet.empty in
    let filter := ConstraintSet.filter (is_declared_cstr_levels lvls) in
    make prefix (ConstraintSet.union (filter au.2) (filter av.2)).
End AUContext.

Module ContextSet.
  Definition t := LevelSet.t × ConstraintSet.t.

  Definition levels : t -> LevelSet.t := fst.
  Definition constraints : t -> ConstraintSet.t := snd.

  Definition empty : t := (LevelSet.empty, ConstraintSet.empty).

  Definition is_empty (uctx : t)
    := LevelSet.is_empty (fst uctx) && ConstraintSet.is_empty (snd uctx).

  Definition Equal (x y : t) : Prop :=
    x.1 =_lset y.1 /\ x.2 =_cset y.2.

  Definition equal (x y : t) : bool :=
    x.1 ==_lset y.1 && x.2 ==_cset y.2.

  Definition Subset (x y : t) : Prop :=
    LevelSet.Subset (levels x) (levels y) /\
    ConstraintSet.Subset (constraints x) (constraints y).

  Definition subset (x y : t) : bool :=
    LevelSet.subset (levels x) (levels y) &&
    ConstraintSet.subset (constraints x) (constraints y).

  Definition inter (x y : t) : t :=
    (LevelSet.inter (levels x) (levels y),
      ConstraintSet.inter (constraints x) (constraints y)).

  Definition inter_spec (x y : t) :
    Subset (inter x y) x /\
      Subset (inter x y) y /\
      forall z, Subset z x -> Subset z y -> Subset z (inter x y).
  Proof.
    split; last split.
    1,2: split=> ?; [move=> /LevelSet.inter_spec [//]|move=> /ConstraintSet.inter_spec [//]].
    move=> ? [??] [??]; split=> ??;
    [apply/LevelSet.inter_spec|apply/ConstraintSet.inter_spec]; split; auto.
  Qed.

  Definition union (x y : t) : t :=
    (LevelSet.union (levels x) (levels y), ConstraintSet.union (constraints x) (constraints y)).

  Definition union_spec (x y : t) :
    Subset x (union x y) /\
      Subset y (union x y) /\
      forall z, Subset x z -> Subset y z -> Subset (union x y) z.
  Proof.
    split; last split.
    1,2: split=> ??; [apply/LevelSet.union_spec|apply/ConstraintSet.union_spec ]; by constructor.
    move=> ? [??] [??]; split=> ?;
    [move=>/LevelSet.union_spec|move=>/ConstraintSet.union_spec]=>-[]; auto.
  Qed.

  Lemma equal_spec s s' : equal s s' <-> Equal s s'.
  Proof.
    rewrite /equal/Equal/is_true Bool.andb_true_iff LevelSet.equal_spec ConstraintSet.equal_spec.
    reflexivity.
  Qed.

  Lemma subset_spec s s' : subset s s' <-> Subset s s'.
  Proof.
    rewrite /subset/Subset/is_true Bool.andb_true_iff LevelSet.subset_spec ConstraintSet.subset_spec.
    reflexivity.
  Qed.

  Lemma subsetP s s' : reflect (Subset s s') (subset s s').
  Proof.
    generalize (subset_spec s s').
    destruct subset; case; constructor; intuition.
  Qed.
End ContextSet.

Export (hints) ContextSet.

Notation "(=_cs)" := ContextSet.Equal (at level 0).
Notation "(⊂_cs)" := ContextSet.Subset (at level 0).
Infix "=_cs" := ContextSet.Equal (at level 30).
Infix "⊂_cs" := ContextSet.Subset (at level 30).
Notation "(==_cs)" := ContextSet.equal (at level 0).
Notation "(⊂?_cs)" := ContextSet.subset (at level 0).
Infix "==_cs" := ContextSet.equal (at level 30).
Infix "⊂?_cs" := ContextSet.subset (at level 30).

Lemma incl_cs_refl cs : cs ⊂_cs cs.
Proof.
  split; [lsets|csets].
Qed.

Lemma incl_cs_trans cs1 cs2 cs3 : cs1 ⊂_cs cs2 -> cs2 ⊂_cs cs3 -> cs1 ⊂_cs cs3.
Proof.
  intros [? ?] [? ?]; split; [lsets|csets].
Qed.

Lemma empty_contextset_subset u : ContextSet.empty ⊂_cs u.
Proof.
  red. split; cbn; [lsets|csets].
Qed.

(* Variance info is needed to do full universe polymorphism *)
Module Variance.
  (** A universe position in the instance given to a cumulative
     inductive can be the following. Note there is no Contralvariant
     case because [forall x : A, B <= forall x : A', B'] requires [A =
     A'] as opposed to [A' <= A]. *)
  Inductive t :=
  | Irrelevant : t
  | Covariant : t
  | Invariant : t.
  Derive NoConfusion EqDec for t.

  (* val check_subtype : t -> t -> bool *)
  (* val sup : t -> t -> t *)
End Variance.

(** What to check of two instances *)
Variant opt_variance :=
  AllEqual | AllIrrelevant | Variance of list Variance.t.

Inductive universes_decl : Type :=
| Monomorphic_ctx
| Polymorphic_ctx (cst : AUContext.t).

Derive NoConfusion for universes_decl.

Definition levels_of_udecl u :=
  match u with
  | Monomorphic_ctx => LevelSet.empty
  | Polymorphic_ctx ctx => AUContext.levels ctx
  end.

Definition constraints_of_udecl u :=
  match u with
  | Monomorphic_ctx => ConstraintSet.empty
  | Polymorphic_ctx ctx => snd (snd (AUContext.repr ctx))
  end.

Declare Scope univ_scope.
Delimit Scope univ_scope with u.

Section Univ.
  Context {cf: checker_flags}.

  Inductive satisfies0 (v : valuation) : LevelConstraint.t -> Prop :=
  | satisfies0_Lt (l l' : Level.t) (z : Z) : (Z.of_nat (val v l) <= Z.of_nat (val v l') - z)%Z
                         -> satisfies0 v (l, ConstraintType.Le z, l')
  | satisfies0_Eq (l l' : Level.t) : val v l = val v l'
                         -> satisfies0 v (l, ConstraintType.Eq, l').

  Definition satisfies v : ConstraintSet.t -> Prop :=
    ConstraintSet.For_all (satisfies0 v).

  Lemma satisfies_union v φ1 φ2 :
    satisfies v (CS.union φ1 φ2)
    <-> (satisfies v φ1 /\ satisfies v φ2).
  Proof.
    unfold satisfies. split.
    - intros H; split; intros c Hc; apply H; now apply CS.union_spec.
    - intros [H1 H2] c Hc; apply CS.union_spec in Hc; destruct Hc; auto.
  Qed.

  Lemma satisfies_subset φ φ' val :
    ConstraintSet.Subset φ φ' ->
    satisfies val φ' ->
    satisfies val φ.
  Proof using Type.
    intros sub sat ? isin.
    apply sat, sub; auto.
  Qed.

  Definition consistent ctrs := exists v, satisfies v ctrs.

  Definition consistent_extension_on cs cstr :=
    forall v, satisfies v (ContextSet.constraints cs) -> exists v',
        satisfies v' cstr /\
          LevelSet.For_all (fun l => val v l = val v' l) (ContextSet.levels cs).

  Lemma consistent_extension_on_empty Σ :
    consistent_extension_on Σ CS.empty.
  Proof.
    move=> v hv; exists v; split; [move=> ? /CS.empty_spec[]| move=> ??//].
  Qed.

  Lemma fold_right_ext {A B} (f g : B -> A -> A) acc acc' l l' :
    (forall x y, f x y = g x y) -> acc = acc' -> l = l' ->
    fold_right f acc l = fold_right g acc' l'.
  Proof.
    intros hfg -> ->; induction l'; cbn; auto; congruence.
  Qed.

  Lemma fold_right_map {A B C} (f : B -> A -> A) (g : C -> B) acc l :
    fold_right (fun x acc => f (g x) acc) acc l =
    fold_right (fun x acc => f x acc) acc (List.map g l).
  Proof.
    induction l; cbn; auto. congruence.
  Qed.

  Lemma subset_levels_exprs {le levels} :
    LevelSet.Subset (LevelExprSet.levels le) levels ->
    forall e, LevelExprSet.In e le -> LevelSet.In e.1 levels.
  Proof.
    intros hs e hin.
    destruct e as [l k].
    apply (hs l). clear hs.
    unfold LevelExprSet.levels.
    revert hin.
    eapply LevelExprSetProp.fold_rec.
    - intros s' emp hin. now specialize (emp _ hin).
    - intros x a s' s'' hin hnin hadd hk. intros hin'.
      rewrite LevelSet.add_spec.
      apply hadd in hin'. destruct hin'. subst. now left.
      firstorder.
  Qed.

  Definition max_ne_list x l :=
    fold_right Nat.max x l.

  Lemma fold_right_assoc {A} (f : A -> A -> A) acc acc' l :
    (forall x y z, f x (f y z) = f y (f x z)) ->
    fold_right f (f acc acc') l = f acc (fold_right f acc' l).
  Proof.
    intros hf. induction l in acc |- *; cbn; auto.
    now rewrite IHl hf.
  Qed.

  Lemma fold_right_assoc_comm {A} (f : A -> A -> A) acc l :
    (forall x y, f x y = f y x) ->
    (forall x y z, f x (f y z) = f y (f x z)) ->
    fold_right f acc l = fold_right f acc (List.rev l).
  Proof.
    intros hf hf'. induction l in acc |- *; cbn; auto.
    rewrite fold_right_app /= -IHl fold_right_assoc //.
  Qed.

  Lemma max_ne_list_rev {x l} : max_ne_list x l = max_ne_list x (List.rev l).
  Proof.
    unfold max_ne_list.
    rewrite fold_right_assoc_comm //; lia.
  Qed.

  Lemma val_max (l : Universe.t) (v : valuation) :
    val v l = let nel := to_nonempty_list l in
      max_ne_list (val v nel.1) (List.map (val v) nel.2).
  Proof.
    cbn.
    rewrite val_fold_right. unfold Universe.exprs.
    rewrite fold_right_map max_ne_list_rev /max_ne_list map_rev //.
  Qed.

  Lemma val_eq_level_expr v v' levels :
    LevelSet.For_all (fun l : LevelSet.elt => val v l = val v' l) levels ->
    forall le : LevelExpr.t, LevelSet.In le.1 levels -> val v le = val v' le.
  Proof.
    intros hl [l k] hin; cbn.
    rewrite hl //.
  Qed.

  Lemma val_eq_levels_alg v v' levels :
    LevelSet.For_all (fun l : LevelSet.elt => val v l = val v' l) levels ->
    forall le : Universe.t,
    LevelSet.Subset (LevelExprSet.levels le) levels ->
    val v le = val v' le.
  Proof.
    move=> hl le /subset_levels_exprs sub.
    rewrite !val_max.
    move: (to_nonempty_list_spec le). destruct to_nonempty_list as [hd tl]. cbn.
    intros heq. f_equal.
    - cbn. eapply val_eq_level_expr; tea.
      eapply sub.
      apply LevelExprSetFact.elements_2. rewrite -heq. now left.
    - eapply map_ext_in => x inx.
      eapply val_eq_level_expr; tea.
      apply sub, LevelExprSetFact.elements_2. rewrite -heq. now right.
  Qed.

  (* Lemma consistent_extension_on_union X cstrs
  (wfX : forall c, CS.In c X.2 -> LS.Subset (LevelExprSet.levels c.1.1) X.1 /\ LS.Subset (LevelExprSet.levels c.2) X.1) :
  consistent_extension_on X cstrs ->
  consistent_extension_on X (CS.union cstrs X.2).
Proof.
  move=> hext v /[dup] vsat /hext [v' [v'sat v'eq]].
  exists v'; split=> //.
  apply/satisfies_union; split=> //.
  move=> c hc. destruct (wfX c hc).
  destruct (vsat c hc); constructor; cbn in *.
  2:{ rewrite -(val_eq_levels_alg v v' _ v'eq l) //.
      rewrite -(val_eq_levels_alg v v' _ v'eq l') //. }
  rewrite -(val_eq_levels_alg v v' _ v'eq l) //.
  rewrite -(val_eq_levels_alg v v' _ v'eq l') //.
Qed. *)

  Lemma consistent_extension_on_union X cstrs
    (wfX : forall c, CS.In c X.2 -> LS.In c.1.1 X.1 /\ LS.In c.2 X.1) :
    consistent_extension_on X cstrs ->
    consistent_extension_on X (CS.union cstrs X.2).
  Proof.
    move=> hext v /[dup] vsat /hext [v' [v'sat v'eq]].
    exists v'; split=> //.
    apply/satisfies_union; split=> //.
    move=> c hc. destruct (wfX c hc).
    (* destruct (vsat c hc); constructor; cbn in *.
    2:{ rewrite -(val_eq_levels_alg v v' _ v'eq l) //.
        rewrite -(val_eq_levels_alg v v' _ v'eq l') //. }
    rewrite -(val_eq_levels_alg v v' _ v'eq l) //.
    rewrite -(val_eq_levels_alg v v' _ v'eq l') //. *)
    destruct (vsat c hc); constructor; rewrite -!v'eq //.
  Qed.

  Definition leq0_universe_n n φ (u u' : Universe.t) :=
    forall v, satisfies v φ -> (Z.of_nat (val v u) <= Z.of_nat (val v u') - n)%Z.

  Definition leq_universe_n n φ (u u' : Universe.t) :=
    if check_univs then leq0_universe_n n φ u u' else True.

  Definition eq0_universe φ (u u' : Universe.t) :=
    forall v, satisfies v φ -> val v u = val v u'.

  Definition eq_universe {cf} φ (u u' : Universe.t) :=
    if check_univs then eq0_universe φ u u' else True.

  Definition lt_universe := leq_universe_n 1.
  Definition leq_universe := leq_universe_n 0.

  Lemma leq_universe_leq_universe_n (φ : ConstraintSet.t) u u' :
    leq_universe φ u u' <-> leq_universe_n 0 φ u u'.
  Proof. intros. reflexivity. Qed.

  (* ctrs are "enforced" by φ *)

  Definition valid_constraints0 φ ctrs
    := forall v, satisfies v φ -> satisfies v ctrs.

  Definition valid_constraints φ ctrs
    := if check_univs then valid_constraints0 φ ctrs else True.

  Definition compare_universe φ (pb : conv_pb) :=
    match pb with
    | Conv => eq_universe φ
    | Cumul => leq_universe φ
    end.

  Ltac unfold_univ_rel0 :=
    unfold eq0_universe, leq0_universe_n, valid_constraints0 in *;
    try (
      match goal with |- forall v : valuation, _ -> _ => idtac end;
      intros v Hv;
      repeat match goal with H : forall v : valuation, _ -> _ |- _ => specialize (H v Hv) end;
      cbnr
    ).

  Ltac unfold_univ_rel :=
    unfold eq_universe, leq_universe, lt_universe, leq_universe_n, valid_constraints in *;
    destruct check_univs; [unfold_univ_rel0 | trivial].

  Lemma valid_subset φ φ' ctrs
    : ConstraintSet.Subset φ φ' -> valid_constraints φ ctrs
      ->  valid_constraints φ' ctrs.
  Proof using Type.
    unfold_univ_rel.
    intros Hφ H v Hv. apply H.
    intros ctr Hc. apply Hv. now apply Hφ.
  Qed.

  Lemma switch_minus (x y z : Z) : (x <= y - z <-> x + z <= y)%Z.
  Proof using Type. split; lia. Qed.

  (** **** Lemmas about eq and leq **** *)

  Global Instance eq_universe_refl φ : Reflexive (eq_universe φ).
  Proof using Type.
    intros u; unfold_univ_rel.
  Qed.

  Global Instance leq_universe_refl φ : Reflexive (leq_universe φ).
  Proof using Type.
    intros u; unfold_univ_rel. lia.
  Qed.

  Global Instance eq_universe_sym φ : Symmetric (eq_universe φ).
  Proof using Type.
    intros u u' H; unfold_univ_rel.
    lia.
  Qed.

  Global Instance eq_universe_trans φ : Transitive (eq_universe φ).
  Proof using Type.
    intros u u' u'' H1 H2; unfold_univ_rel.
    lia.
  Qed.

  Global Instance leq_universe_n_trans n φ : Transitive (leq_universe_n (Z.of_nat n) φ).
  Proof using Type.
    intros u u' u'' H1 H2; unfold_univ_rel.
    lia.
  Qed.

  Global Instance leq_universe_trans φ : Transitive (leq_universe φ).
  Proof using Type. apply (leq_universe_n_trans 0). Qed.

  Global Instance lt_universe_trans φ : Transitive (lt_universe φ).
  Proof using Type. apply (leq_universe_n_trans 1). Qed.

  Lemma eq0_leq0_universe φ u u' :
    eq0_universe φ u u' <-> leq0_universe_n 0 φ u u' /\ leq0_universe_n 0 φ u' u.
  Proof using Type.
    split.
    - intros H. split; unfold_univ_rel0; lia.
    - intros [H1 H2]. unfold_univ_rel0; lia.
  Qed.

  Lemma eq_universe_leq_universe φ u u' :
    eq_universe φ u u' <-> leq_universe φ u u' /\ leq_universe φ u' u.
  Proof using Type.
    unfold_univ_rel => //.
    apply eq0_leq0_universe.
  Qed.

  Lemma leq_universe_sup_l φ u1 u2 : leq_universe φ u1 (Universe.sup u1 u2).
  Proof using Type. unfold_univ_rel. rewrite val_sup; lia. Qed.

  Lemma leq_universe_sup_r φ u1 u2 : leq_universe φ u2 (Universe.sup u1 u2).
  Proof using Type. unfold_univ_rel. rewrite val_sup; lia. Qed.

  Lemma leq_universe_sup_mon φ u1 u1' u2 u2' : leq_universe φ u1 u1' -> leq_universe φ u2 u2' ->
    leq_universe φ (Universe.sup u1 u2) (Universe.sup u1' u2').
  Proof using Type.
    intros H1 H2; unfold_univ_rel.
    rewrite !val_sup. lia.
  Qed.

  Global Instance eq_leq_universe φ : subrelation (eq_universe φ) (leq_universe φ).
  Proof using Type.
    intros u u'. apply eq_universe_leq_universe.
  Qed.

  Global Instance eq_universe_equivalence φ : Equivalence (eq_universe φ) := Build_Equivalence _ _ _ _.

  Global Instance leq_universe_preorder φ : PreOrder (leq_universe φ) := Build_PreOrder _ _ _.

  Global Instance lt_universe_irrefl {c: check_univs} φ (H: consistent φ) : Irreflexive (lt_universe φ).
  Proof using Type.
    intro u. unfold complement.
    unfold_univ_rel => //.
    destruct H as [v Hv]; intros nH; specialize (nH v Hv); lia.
  Qed.

  Global Instance lt_universe_str_order {c: check_univs} φ (H: consistent φ) : StrictOrder (lt_universe φ).
  Proof.
    refine (Build_StrictOrder _ _ _).
    now unshelve eapply lt_universe_irrefl.
  Qed.

  Global Instance leq_universe_antisym φ : Antisymmetric _ (eq_universe φ) (leq_universe φ).
  Proof using Type. intros t u tu ut. now apply eq_universe_leq_universe. Qed.

  Global Instance leq_universe_partial_order φ
    : PartialOrder (eq_universe φ) (leq_universe φ).
  Proof.
    intros x y; split; apply eq_universe_leq_universe.
  Defined.


  Global Instance compare_universe_subrel φ pb : subrelation (eq_universe φ) (compare_universe φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_universe_refl φ pb : Reflexive (compare_universe φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_universe_trans φ pb : Transitive (compare_universe φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_universe_preorder φ pb : PreOrder (compare_universe φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Definition eq_leq_universe' φ u u'
    := @eq_leq_universe φ u u'.
  Definition leq_universe_refl' φ u
    := @leq_universe_refl φ u.

  Hint Resolve eq_leq_universe' leq_universe_refl' : core.


  Lemma cmp_universe_subset φ φ' pb t u :
    ConstraintSet.Subset φ φ' -> compare_universe φ pb t u -> compare_universe φ' pb t u.
  Proof using Type.
    intros Hctrs.
    destruct pb, t, u; cbnr; trivial.
    all: intros H; unfold_univ_rel;
    apply H.
    all: eapply satisfies_subset; eauto.
  Qed.

  Lemma eq_universe_subset φ φ' t u
    : ConstraintSet.Subset φ φ'
      -> eq_universe φ t u -> eq_universe φ' t u.
  Proof using Type. apply cmp_universe_subset with (pb := Conv). Qed.

  Lemma leq_universe_subset φ φ' t u
    : ConstraintSet.Subset φ φ'
      -> leq_universe φ t u -> leq_universe φ' t u.
  Proof using Type. apply cmp_universe_subset with (pb := Cumul). Qed.


End Univ.

Ltac unfold_univ_rel0 :=
    unfold eq0_universe, leq0_universe_n, valid_constraints0 in *;
    try (
      match goal with |- forall v : valuation, _ -> _ => idtac end;
      intros v Hv;
      repeat match goal with H : forall v : valuation, _ -> _ |- _ => specialize (H v Hv) end;
      cbnr
    ).

Ltac unfold_univ_rel :=
  unfold eq_universe, leq_universe, lt_universe, leq_universe_n, valid_constraints in *;
  destruct check_univs; [unfold_univ_rel0 | trivial].


Module Sort.
  Inductive t_ {univ} :=
    sProp | sSProp | sType (_ : univ).
  Derive NoConfusion for t_.
  Arguments t_ : clear implicits.

  Definition t := t_ Universe.t.

  Inductive family : Set :=
  | fSProp
  | fProp
  | fType.
  Derive NoConfusion EqDec for family.

  Definition eqb {univ} `{ReflectEq univ} (u1 u2 : t_ univ) : bool :=
    match u1, u2 with
    | sSProp, sSProp => true
    | sProp, sProp => true
    | sType e1, sType e2 => eqb e1 e2
    | _, _ => false
    end.

  #[global, program] Instance reflect_eq_sort {univ} `{ReflectEq univ} : ReflectEq (t_ univ) :=
    { eqb := eqb }.
  Next Obligation.
    destruct x, y; cbn; try constructor; auto; try congruence.
    destruct (eqb_spec u u0); constructor. now f_equal.
    congruence.
  Qed.

  #[global] Instance eq_dec_sort {univ} `{EqDec univ} : EqDec (t_ univ) := ltac:(intros s s'; decide equality).

  Definition map {u u'} (f : u -> u') s :=
    match s with
    | sType u => sType (f u)
    | sProp => sProp
    | sSProp => sSProp
    end.

  Definition on_sort {univ} {T} (P: univ -> T) (def: T) (s : t_ univ) :=
    match s with
    | sProp | sSProp => def
    | sType l => P l
    end.

  (** Test if the universe is a lub of levels or contains +n's. *)
  Definition is_levels (s : t) : bool :=
    match s with
    | sSProp | sProp => true
    | sType l => Universe.is_levels l
    end.

  (** Test if the universe is a level or an algebraic universe. *)
  Definition is_level (s : t) : bool :=
    match s with
    | sSProp | sProp => true
    | sType l => Universe.is_level l
    end.

  Definition is_sprop {univ} (s : t_ univ) : bool :=
    match s with
      | sSProp => true
      | _ => false
    end.

  Definition is_prop {univ} (s : t_ univ) : bool :=
    match s with
      | sProp => true
      | _ => false
    end.

  Definition is_propositional {univ} (s : t_ univ) : bool :=
    match s with
      | sProp | sSProp => true
      | _ => false
    end.

  Lemma is_prop_propositional {univ} (s : t_ univ) :
    is_prop s -> is_propositional s.
  Proof. now destruct s. Qed.
  Lemma is_sprop_propositional {univ} (s : t_ univ) :
    is_sprop s -> is_propositional s.
  Proof. now destruct s. Qed.

  Definition is_type_sort {univ} (s : t_ univ) : bool :=
    match s with
      | sType _ => true
      | _ => false
    end.

  Definition type0 : t := sType (Universe.make LevelExpr.set).
  Definition type1 : t := sType (Universe.make LevelExpr.type1).

  Definition of_levels (l : PropLevel.t + Level.t) : t :=
    match l with
    | inl PropLevel.lSProp => sSProp
    | inl PropLevel.lProp => sProp
    | inr l => sType (Universe.make' l)
    end.

  (** The universe strictly above FOR TYPING (not cumulativity) *)

  Definition super_ {univ} type1 univ_succ (s : t_ univ) : t_ univ :=
    match s with
    | sSProp | sProp => sType type1
    | sType l => sType (univ_succ l)
    end.
  Definition super : t -> t := super_ (Universe.make LevelExpr.type1) Universe.succ.
  Definition csuper := super_ 1 S.

  Definition sup_ {univ} univ_sup (s s' : t_ univ) : t_ univ :=
    match s, s' with
    | sSProp, s' => s'
    | sProp, sSProp => sProp
    | sProp, s' => s'
    | sType u1, sType u2 => sType (univ_sup u1 u2)
    | sType _ as s, _ => s
    end.
  Definition sup : t -> t -> t := sup_ Universe.sup.
  Definition csup := sup_ Nat.max.

  (** Type of a product *)
  Definition sort_of_product_ {univ} univ_sup (domsort rangsort : t_ univ) : t_ univ :=
    match rangsort with
    | sSProp | sProp => rangsort
    (* Prop and SProp impredicativity *)
    | _ => Sort.sup_ univ_sup domsort rangsort
    end.
  Definition sort_of_product : t -> t -> t := sort_of_product_ Universe.sup.
  Definition csort_of_product := sort_of_product_ Nat.max.

  Definition get_is_level (s : t) : option Level.t :=
    match s with
    | sSProp => None
    | sProp => None
    | sType l => Universe.get_is_level l
    end.

  Definition to_family {univ} (s : t_ univ) :=
    match s with
    | sSProp => fSProp
    | sProp => fProp
    | sType _ => fType
    end.

  Definition to_csort v s :=
    match s with
    | sSProp => sSProp
    | sProp => sProp
    | sType u => sType (val v u)
    end.

  Lemma to_family_to_csort s v :
    to_family (to_csort v s) = to_family s.
  Proof.
    destruct s; cbnr.
  Qed.

  Lemma sType_super_ {univ type1 univ_succ} (s : t_ univ) :
    to_family (super_ type1 univ_succ s) = fType.
  Proof. now destruct s. Qed.

  Lemma sType_super (s : t) :
    to_family (super s) = fType.
  Proof. apply sType_super_. Qed.

  Inductive lt_ {univ univ_lt} : t_ univ -> t_ univ -> Prop :=
  | ltPropSProp : lt_ sProp sSProp
  | ltPropType s : lt_ sProp (sType s)
  | ltSPropType s : lt_ sSProp (sType s)
  | ltTypeType s1 s2 : univ_lt s1 s2 -> lt_ (sType s1) (sType s2).
  Derive Signature for lt_.
  Arguments lt_ {univ} univ_lt.

  Definition lt := lt_ Universe.lt.
  Definition clt := lt_ Nat.lt.

  Module OT <: OrderedType.
    Definition t := t.
    #[local] Definition eq : t -> t -> Prop := eq.
    #[local] Definition eq_equiv : Equivalence eq := _.
    Definition lt := lt.
    #[local] Instance lt_strorder : StrictOrder lt.
    Proof.
      constructor.
      - intros [| |] X; inversion X.
        now eapply irreflexivity in H1.
      - intros [| |] [| |] [| |] X1 X2;
          inversion X1; inversion X2; constructor.
        subst.
        etransitivity; tea.
    Qed.

    Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
    Proof.
      intros x y e z t e'. hnf in * |- ; subst. reflexivity.
    Qed.
    Definition compare (x y : t) : comparison
      := match x, y with
          | sProp, sProp => Eq
          | sProp, _ => Lt
          | _, sProp => Gt
          | sSProp, sSProp => Eq
          | sSProp, _ => Lt
          | _, sSProp => Gt
          | sType x, sType y => LevelExprSet.compare x y
          end.
    Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
    Proof.
      cbv [compare eq].
      destruct x, y.
      all: lazymatch goal with
            | [ |- context[LevelExprSet.compare ?x ?y] ]
              => destruct (LevelExprSet.compare_spec x y)
            | _ => idtac
            end.
      all: lazymatch goal with
            | [ H : LevelExprSet.eq (?f ?x) (?f ?y) |- _ ]
              => apply LevelExprSet.eq_leibniz in H;
                is_var x; is_var y; destruct x, y; cbn in H; subst
            | _ => idtac
            end.
      all: repeat constructor; try apply f_equal; try assumption.
      f_equal; apply Eqdep_dec.UIP_dec; decide equality.
    Qed.
    Definition eq_dec (x y : t) : {x = y} + {x <> y}.
    Proof. repeat decide equality. apply Universe.eq_dec_univ0. Defined.
  End OT.
  Module OTOrig <: OrderedTypeOrig := Backport_OT OT.
End Sort.


Module SortMap := FMapAVL.Make Sort.OTOrig.
Module SortMapFact := FMapFacts.WProperties SortMap.
Module SortMapExtraFact := FSets.WFactsExtra_fun Sort.OTOrig SortMap SortMapFact.F.
Module SortMapDecide := FMapAVL.Decide Sort.OTOrig SortMap.

Notation sProp := Sort.sProp.
Notation sSProp := Sort.sSProp.
Notation sType := Sort.sType.
Notation sort := Sort.t.

Notation "⟦ u ⟧_ v" := (Sort.to_csort v u) (at level 0, format "⟦ u ⟧_ v", v name) : univ_scope.


Lemma val_sort_sup v s1 s2 :
  Sort.to_csort v (Sort.sup s1 s2) = Sort.csup (Sort.to_csort v s1) (Sort.to_csort v s2).
Proof.
  destruct s1 as [ | | u1]; destruct s2 as [ | | u2]; cbnr.
  f_equal. apply val_sup.
Qed.

Lemma is_prop_val s :
  Sort.is_prop s -> forall v, Sort.to_csort v s = Sort.sProp.
Proof.
  destruct s => //.
Qed.

Lemma is_sprop_val s :
  Sort.is_sprop s -> forall v, Sort.to_csort v s = Sort.sSProp.
Proof.
  destruct s => //.
Qed.


Lemma val_is_prop s v :
  Sort.to_csort v s = sProp <-> Sort.is_prop s.
Proof.
  destruct s => //.
Qed.

Lemma val_is_sprop s v :
  Sort.to_csort v s = sSProp <-> Sort.is_sprop s.
Proof.
  destruct s => //.
Qed.

Lemma is_prop_and_is_sprop_val_false s :
  Sort.is_prop s = false -> Sort.is_sprop s = false ->
  forall v, ∑ n, Sort.to_csort v s = sType n.
Proof.
  intros Hp Hsp v.
  destruct s => //. simpl. eexists; eauto.
Qed.

Lemma val_is_prop_false s v n :
  Sort.to_csort v s = sType n -> Sort.is_prop s = false.
Proof.
  destruct s => //.
Qed.

Lemma get_is_level_correct s l :
  Sort.get_is_level s = Some l -> s = sType (Universe.make' l).
Proof.
  intro H; destruct s => //=.
  f_equal; now apply universe_get_is_level_correct.
Qed.

Lemma eqb_true_iff (s s' : sort) :
  eqb s s' <-> s = s'.
Proof.
  split. apply /eqb_spec. eapply introP. apply /eqb_spec.
Qed.

Lemma sup_comm x1 x2 :
  Sort.sup x1 x2 = Sort.sup x2 x1.
Proof.
  destruct x1,x2;auto.
  cbn;apply f_equal;apply sup0_comm.
Qed.

Lemma is_not_prop_and_is_not_sprop {univ} (s : Sort.t_ univ) :
  Sort.is_prop s = false -> Sort.is_sprop s = false ->
  ∑ s', s = sType s'.
Proof.
  intros Hp Hsp.
  destruct s => //. now eexists.
Qed.

Lemma is_prop_sort_sup x1 x2 :
  Sort.is_prop (Sort.sup x1 x2)
  -> Sort.is_prop x2 \/ Sort.is_sprop x2 .
Proof. destruct x1,x2;auto. Qed.

Lemma is_prop_sort_sup' x1 x2 :
  Sort.is_prop (Sort.sup x1 x2)
  -> Sort.is_prop x1 \/ Sort.is_sprop x1 .
Proof. destruct x1,x2;auto. Qed.

Lemma is_prop_or_sprop_sort_sup x1 x2 :
  Sort.is_sprop (Sort.sup x1 x2) -> Sort.is_sprop x2.
Proof. destruct x1,x2;auto. Qed.

Lemma is_prop_sort_sup_prop x1 x2 :
  Sort.is_prop x1 && Sort.is_prop x2 ->
  Sort.is_prop (Sort.sup x1 x2).
Proof. destruct x1,x2;auto. Qed.

Lemma is_prop_or_sprop_sort_sup_prop x1 x2 :
  Sort.is_sprop x1 && Sort.is_sprop x2 ->
  Sort.is_sprop (Sort.sup x1 x2).
Proof. destruct x1,x2;auto. Qed.

Lemma is_prop_sup s s' :
  Sort.is_prop (Sort.sup s s') ->
  Sort.is_propositional s /\ Sort.is_propositional s'.
Proof. destruct s, s'; auto. Qed.

Lemma is_sprop_sup_iff s s' :
  Sort.is_sprop (Sort.sup s s') <->
  (Sort.is_sprop s /\ Sort.is_sprop s').
Proof. split; destruct s, s' => //=; intuition. Qed.

Lemma is_type_sup_r s1 s2 :
  Sort.is_type_sort s2 ->
  Sort.is_type_sort (Sort.sup s1 s2).
Proof. destruct s2; try absurd; destruct s1; cbnr; intros; absurd. Qed.

Lemma is_prop_sort_prod x2 x3 :
  Sort.is_prop (Sort.sort_of_product x2 x3)
  -> Sort.is_prop x3.
Proof.
  unfold Sort.sort_of_product.
  destruct x3;cbn;auto.
  intros;simpl in *;destruct x2;auto.
Qed.

Lemma is_sprop_sort_prod x2 x3 :
  Sort.is_sprop (Sort.sort_of_product x2 x3)
  -> Sort.is_sprop x3.
Proof.
  unfold Sort.sort_of_product.
  destruct x3;cbn;auto.
  intros;simpl in *;destruct x2;auto.
Qed.



Section SortCompare.
  Context {cf}.
  Definition leq_sort_n_ {univ} (leq_universe_n : Z -> univ -> univ -> Prop) n s s' : Prop :=
    match s, s' with
    | sProp,   sProp
    | sSProp,  sSProp => (n = 0)%Z
    | sType u, sType u' => leq_universe_n n u u'
    | sProp,   sType u => prop_sub_type
    | _, _ => False
    end.

  Definition leq_sort_n n φ := leq_sort_n_ (fun n => leq_universe_n n φ) n.
  Definition lt_sort := leq_sort_n 1.
  Definition leq_sort := leq_sort_n 0.

  Definition leqb_sort_n_ {univ} (leqb_universe_n : bool -> univ -> univ -> bool) b s s' : bool :=
    match s, s' with
    | sProp,   sProp
    | sSProp,  sSProp => negb b
    | sType u, sType u' => leqb_universe_n b u u'
    | sProp,   sType u => prop_sub_type
    | _, _ => false
    end.

  Definition eq_sort_ {univ} (eq_universe : univ -> univ -> Prop) s s' : Prop :=
    match s, s' with
    | sProp,   sProp
    | sSProp,  sSProp => True
    | sType u, sType u' => eq_universe u u'
    | _, _ => False
    end.

  Definition eq_sort φ := eq_sort_ (eq_universe φ).

  Definition eqb_sort_ {univ} (eqb_universe : univ -> univ -> bool) s s' : bool :=
    match s, s' with
    | sProp,   sProp
    | sSProp,  sSProp => true
    | sType u, sType u' => eqb_universe u u'
    | _, _ => false
    end.

  Definition compare_sort φ (pb : conv_pb) :=
    match pb with
    | Conv => eq_sort φ
    | Cumul => leq_sort φ
    end.

  Lemma leq_sort_leq_sort_n (φ : ConstraintSet.t) s s' :
    leq_sort φ s s' <-> leq_sort_n 0 φ s s'.
  Proof using Type. intros. reflexivity. Qed.

  Lemma compare_sort_type φ pb u u' :
    compare_sort φ pb (sType u) (sType u') = compare_universe φ pb u u'.
  Proof. now destruct pb. Qed.

  Section GeneralLemmas.
    Context {univ} {leq_universe_n : Z -> univ -> univ -> Prop} {eq_universe : univ -> univ -> Prop}.

    Let leq_sort_n := leq_sort_n_ leq_universe_n.
    Let lt_sort := leq_sort_n_ leq_universe_n 1.
    Let leq_sort := leq_sort_n_ leq_universe_n 0.
    Let eq_sort := eq_sort_ eq_universe.
    Notation "x <_ n  y" := (leq_sort_n n x y) (at level 10, n name).
    Notation "x < y" := (lt_sort x y).
    Notation "x <= y" := (leq_sort x y).


    Lemma sort_le_prop_inv s : s <= sProp -> s = sProp.
    Proof using Type. destruct s => //. Qed.

    Lemma sort_le_sprop_inv s : s <= sSProp -> s = sSProp.
    Proof using Type. destruct s => //. Qed.

    Lemma sort_prop_le_inv s : sProp <= s ->
      (s = sProp \/ (prop_sub_type /\ exists n, s = sType n)).
    Proof using Type.
      destruct s => //= Hle.
      - now left.
      - right; split => //; now eexists.
    Qed.

    Lemma sort_sprop_le_inv s : sSProp <= s -> s = sSProp.
    Proof using Type. destruct s => //. Qed.

    Global Instance leq_sort_refl `{Reflexive univ (leq_universe_n 0)} : Reflexive leq_sort.
    Proof using Type. intros []; cbnr. Qed.

    Global Instance eq_sort_refl `{Reflexive univ eq_universe} : Reflexive eq_sort.
    Proof using Type. intros []; cbnr. Qed.

    Global Instance eq_sort_sym `{Symmetric univ eq_universe} : Symmetric eq_sort.
    Proof using Type. intros [] [] => //=. apply H. Qed.

    Global Instance leq_sort_n_trans n `{Transitive univ (leq_universe_n n)} : Transitive (leq_sort_n n).
    Proof using Type.
      intros [] [] [] => //=. apply H.
    Qed.

    Global Instance leq_sort_trans `{Transitive univ (leq_universe_n 0)} : Transitive leq_sort.
    Proof using Type. apply (leq_sort_n_trans 0). Qed.

    Global Instance lt_sort_trans `{Transitive univ (leq_universe_n 1)} : Transitive lt_sort.
    Proof using Type. apply (leq_sort_n_trans 1). Qed.

    Global Instance eq_sort_trans `{Transitive univ eq_universe} : Transitive eq_sort.
    Proof using Type.
      intros [] [] [] => //=. apply H.
    Qed.

    Global Instance leq_sort_preorder `{PreOrder univ (leq_universe_n 0)} : PreOrder leq_sort :=
      Build_PreOrder _ _ _.

    (* Can't be a global instance since it can lead to infinite search *)
    Lemma lt_sort_irrefl : Irreflexive (leq_universe_n 1) -> Irreflexive lt_sort.
    Proof using Type.
      intros H []; unfold complement; cbnr. 1,2: lia. apply H.
    Qed.

    Global Instance lt_sort_str_order `{StrictOrder univ (leq_universe_n 1)} : StrictOrder lt_sort :=
      Build_StrictOrder _ (lt_sort_irrefl _) _.

    Global Instance eq_leq_sort `{subrelation univ eq_universe (leq_universe_n 0)}: subrelation eq_sort leq_sort.
    Proof using Type.
      intros [] [] => //=. apply H.
    Qed.

    Global Instance eq_sort_equivalence `{Equivalence univ eq_universe} : Equivalence eq_sort := Build_Equivalence _ _ _ _.

    Global Instance leq_sort_antisym `{Antisymmetric _ eq_universe (leq_universe_n 0)} : Antisymmetric _ eq_sort leq_sort.
    Proof using Type.
      intros [] [] => //=. apply H.
    Qed.

    Global Instance leq_sort_partial_order `{PartialOrder _ eq_universe (leq_universe_n 0)}: PartialOrder eq_sort leq_sort.
    Proof.
      assert (subrelation eq_universe (leq_universe_n 0)).
      { intros u u' Hu. specialize (H u u'); cbn in H. apply H in Hu. apply Hu. }
      assert (subrelation eq_universe (flip (leq_universe_n 0))).
      { intros u u' Hu. specialize (H u u'); cbn in H. apply H in Hu. apply Hu. }
      intros s s'. split.
      - intro Heq. split.
        + now eapply eq_leq_sort.
        + now eapply eq_leq_sort.
      - intros [Hle Hge]. now eapply leq_sort_antisym.
    Qed.

  End GeneralLemmas.


  (** Universes with linear hierarchy *)
  Definition concrete_sort := Sort.t_ nat.

  (** u + n <= u' *)
  Definition leq_csort_n : Z -> concrete_sort -> concrete_sort -> Prop :=
    leq_sort_n_ (fun n u u' => (Z.of_nat u <= Z.of_nat u' - n)%Z).

  Definition leq_csort := leq_csort_n 0.
  Definition lt_csort := leq_csort_n 1.

  Notation "x <_ n  y" := (leq_csort_n n x y) (at level 10, n name) : univ_scope.
  Notation "x < y" := (lt_csort x y) : univ_scope.
  Notation "x <= y" := (leq_csort x y) : univ_scope.

  Definition is_propositional_or_set s := match s with sSProp | sProp | sType 0 => true | _ => false end.

  Lemma csort_sup_comm s s' : Sort.csup s s' = Sort.csup s' s.
  Proof using Type. destruct s, s' => //=. f_equal; lia. Qed.

  Lemma csort_sup_not_uproplevel s s' :
    ~ Sort.is_propositional s -> ∑ n, Sort.csup s s' = sType n.
  Proof using Type.
    destruct s => //=.
    destruct s'; now eexists.
  Qed.

  Lemma csort_sup_mon s s' v v' : (s <= s')%u -> (sType v <= sType v')%u ->
    (Sort.csup s (sType v) <= Sort.csup s' (sType v'))%u.
  Proof using Type.
    destruct s, s' => //=; intros Hle Hle';
    lia.
  Qed.

  Lemma leq_csort_of_product_mon u u' v v' :
    (u <= u')%u ->
    (v <= v')%u ->
    (Sort.csort_of_product u v <= Sort.csort_of_product u' v')%u.
  Proof using Type.
    intros Hle1 Hle2.
    destruct v, v'; cbn in Hle2 |- *; auto.
    - destruct u'; cbn; assumption.
    - apply csort_sup_mon; assumption.
  Qed.

  Lemma impredicative_csort_product {univ} {univ_sup} {l u} :
    Sort.is_propositional u ->
    Sort.sort_of_product_ (univ := univ) univ_sup l u = u.
  Proof using Type. now destruct u. Qed.

  Lemma leq_sort_sup_l φ u1 s2 :
    let s1 := sType u1 in
    leq_sort φ s1 (Sort.sup s1 s2).
  Proof using Type.
    destruct s2 as [| | u2]; cbnr.
    apply leq_universe_sup_l.
  Qed.

  Lemma leq_sort_sup_r φ s1 u2 :
    let s2 := sType u2 in
    leq_sort φ s2 (Sort.sup s1 s2).
  Proof using Type.
    destruct s1 as [| | u1]; cbnr.
    apply leq_universe_sup_r.
  Qed.

  Lemma leq_sort_product φ (s1 s2 : Sort.t)
    : leq_sort φ s2 (Sort.sort_of_product s1 s2).
  Proof using Type.
    destruct s2 as [| | u2] => //.
    apply leq_sort_sup_r.
  Qed.
  (* Rk: [leq_universe φ s1 (sort_of_product s1 s2)] does not hold due to
      impredicativity. *)


  Global Instance lt_sort_irrefl' {c: check_univs} φ (H: consistent φ) : Irreflexive (lt_sort φ).
  Proof.
    unshelve eapply lt_sort_irrefl.
    now unshelve eapply lt_universe_irrefl.
  Qed.

  Global Instance lt_sort_str_order' {c: check_univs} φ (H: consistent φ) : StrictOrder (lt_sort φ).
  Proof using Type.
    unshelve eapply lt_sort_str_order.
    now unshelve eapply lt_universe_str_order.
  Qed.

  Global Instance compare_sort_subrel φ pb : subrelation (eq_sort φ) (compare_sort φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_sort_refl φ pb : Reflexive (compare_sort φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_sort_trans φ pb : Transitive (compare_sort φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_sort_preorder φ pb : PreOrder (compare_sort φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Definition eq_leq_sort' φ leq_universe eq_universe Hsub u u'
    := @eq_leq_sort φ leq_universe eq_universe Hsub u u'.
  Definition leq_sort_refl' φ leq_universe leq_refl u
    := @leq_sort_refl φ leq_universe leq_refl u.

  Hint Resolve eq_leq_universe' leq_universe_refl' : core.


  Lemma cmp_sort_subset φ φ' pb t u
    : ConstraintSet.Subset φ φ'
      -> compare_sort φ pb t u -> compare_sort φ' pb t u.
  Proof using Type.
    intros Hctrs.
    destruct pb, t, u; cbnr; trivial.
    all: intros H; unfold_univ_rel;
    apply H.
    all: eapply satisfies_subset; eauto.
  Qed.

  Lemma eq_sort_subset ctrs ctrs' t u
    : ConstraintSet.Subset ctrs ctrs'
      -> eq_sort ctrs t u -> eq_sort ctrs' t u.
  Proof using Type. apply cmp_sort_subset with (pb := Conv). Qed.

  Lemma leq_sort_subset ctrs ctrs' t u
    : ConstraintSet.Subset ctrs ctrs'
      -> leq_sort ctrs t u -> leq_sort ctrs' t u.
  Proof using Type. apply cmp_sort_subset with (pb := Cumul). Qed.
End SortCompare.



Definition relevance_of_family (s : Sort.family) :=
  match s with
  | Sort.fSProp => Irrelevant
  | _ => Relevant
  end.

#[global] Opaque relevance_of_family.

Notation rel_of_Type := (relevance_of_family Sort.fType).
Notation relevance_of_sort s := (relevance_of_family (Sort.to_family s)).

Notation isSortRel s rel := (relevance_of_sort s = rel).
Notation isSortRelOpt s relopt :=
  (option_default (fun rel => isSortRel s rel) relopt True).



(** Elimination restriction *)


(** This inductive classifies which eliminations are allowed for inductive types
  in various sorts. *)
Inductive allowed_eliminations : Set :=
  | IntoSProp
  | IntoPropSProp
  | IntoSetPropSProp
  | IntoAny.
Derive NoConfusion EqDec for allowed_eliminations.


Definition is_allowed_elimination_cuniv (allowed : allowed_eliminations) : concrete_sort -> bool :=
  match allowed with
  | IntoSProp => Sort.is_sprop
  | IntoPropSProp => Sort.is_propositional
  | IntoSetPropSProp => is_propositional_or_set
  | IntoAny => fun _ => true
  end.

Definition is_lSet {cf} φ s := eq_sort φ s Sort.type0.
  (* Unfolded definition :
  match s with
  | Sort.sType u =>
    if check_univs then forall v, satisfies v φ -> val v u = 0 else true
  | _ => false
  end. *)

Definition is_allowed_elimination {cf} φ allowed : Sort.t -> Prop :=
  match allowed with
  | IntoSProp => Sort.is_sprop
  | IntoPropSProp => Sort.is_propositional
  | IntoSetPropSProp => fun s => Sort.is_propositional s \/ is_lSet φ s
  | IntoAny => fun s => true
  end.

(* Is [a] a subset of [a']? *)
Definition allowed_eliminations_subset (a a' : allowed_eliminations) : bool :=
  match a, a' with
  | IntoSProp, _
  | IntoPropSProp, (IntoPropSProp | IntoSetPropSProp | IntoAny)
  | IntoSetPropSProp, (IntoSetPropSProp | IntoAny)
  | IntoAny, IntoAny => true
  | _, _ => false
  end.

Lemma allowed_eliminations_subset_impl {cf} φ a a' s
  : allowed_eliminations_subset a a' ->
    is_allowed_elimination φ a s -> is_allowed_elimination φ a' s.
Proof using Type.
  destruct a, a'; cbnr; trivial;
  destruct s; cbnr; trivial;
  intros H1 H2; try absurd; constructor; trivial.
Qed.

Lemma is_allowed_elimination_monotone `{cf : checker_flags} Σ s1 s2 a :
  leq_sort Σ s1 s2 -> is_allowed_elimination Σ a s2 -> is_allowed_elimination Σ a s1.
Proof.
  destruct a, s2 as [| |u2], s1 as [| |u1] => //=. 1: now left.
  intros Hle [H|]; right => //.
  unfold_univ_rel.
  cbn in H.
  lia.
Qed.

Section UnivCF2.
  Context {cf1 cf2 : checker_flags}.

  Lemma valid_config_impl φ ctrs
    : config.impl cf1 cf2 -> @valid_constraints cf1 φ ctrs
      -> @valid_constraints cf2 φ ctrs.
  Proof using Type.
    unfold valid_constraints, config.impl, is_true.
    do 2 destruct check_univs; trivial; cbn => //.
  Qed.

  Lemma cmp_universe_config_impl ctrs pb t u
    : config.impl cf1 cf2
      -> @compare_universe cf1 ctrs pb t u -> @compare_universe cf2 ctrs pb t u.
  Proof using Type.
    unfold config.impl, compare_universe, leq_universe, eq_universe, leq_universe_n, is_true.
    destruct pb; do 2 destruct check_univs => //=.
  Qed.

  Lemma eq_universe_config_impl ctrs t u
    : config.impl cf1 cf2
      -> @eq_universe cf1 ctrs t u -> @eq_universe cf2 ctrs t u.
  Proof using Type. apply cmp_universe_config_impl with (pb := Conv). Qed.

  Lemma leq_universe_config_impl ctrs t u
    : config.impl cf1 cf2
      -> @leq_universe cf1 ctrs t u -> @leq_universe cf2 ctrs t u.
  Proof using Type. apply cmp_universe_config_impl with (pb := Cumul). Qed.

  Lemma cmp_sort_config_impl ctrs pb t u
    : config.impl cf1 cf2
      -> @compare_sort cf1 ctrs pb t u -> @compare_sort cf2 ctrs pb t u.
  Proof using Type.
    unfold compare_sort, leq_sort, eq_sort, eq_sort_, leq_sort_n, leq_sort_n_, is_true.
    destruct pb, t, u => //=.
    - apply eq_universe_config_impl.
    - unfold config.impl. do 2 destruct check_univs, prop_sub_type; cbn => //=.
    - apply leq_universe_config_impl.
  Qed.

  Lemma eq_sort_config_impl ctrs t u
    : config.impl cf1 cf2
      -> @eq_sort cf1 ctrs t u -> @eq_sort cf2 ctrs t u.
  Proof using Type. apply cmp_sort_config_impl with (pb := Conv). Qed.

  Lemma leq_sort_config_impl ctrs t u
    : config.impl cf1 cf2
      -> @leq_sort cf1 ctrs t u -> @leq_sort cf2 ctrs t u.
  Proof using Type. apply cmp_sort_config_impl with (pb := Cumul). Qed.

  (** Elimination restriction *)

  Lemma allowed_eliminations_config_impl φ a s
    : config.impl cf1 cf2 ->
      @is_allowed_elimination cf1 φ a s -> @is_allowed_elimination cf2 φ a s.
  Proof using Type.
    destruct a, s; cbnr; trivial.
    unfold eq_universe, config.impl, is_true.
    do 2 destruct check_univs; cbnr; auto => //.
  Qed.

End UnivCF2.


Ltac unfold_univ_rel ::=
  unfold is_allowed_elimination, is_lSet, valid_constraints,
  compare_sort, eq_sort, leq_sort, lt_sort, leq_sort_n, leq_sort_n_, eq_sort_, leqb_sort_n_, eqb_sort_,
  compare_universe, leq_universe, eq_universe, leq_universe_n in *;
  destruct check_univs; [unfold_univ_rel0 | trivial].

Tactic Notation "unfold_univ_rel" "eqn" ":"ident(H) :=
  unfold is_allowed_elimination, is_lSet, valid_constraints,
  compare_sort, eq_sort, leq_sort, lt_sort, leq_sort_n, leq_sort_n_, eq_sort_, leqb_sort_n_, eqb_sort_,
  compare_universe, leq_universe, eq_universe, leq_universe_n in *;
  destruct check_univs eqn:H; [unfold_univ_rel0 | trivial].

(* Ltac prop_non_prop :=
  match goal with
  | |- context[ Sort.is_prop ?u || Sort.is_sprop ?u]  =>
    destruct (Sort.is_prop u || Sort.is_sprop u)
  | H : context[ Sort.is_prop ?u || Sort.is_sprop ?u] |- _ =>
    destruct (Sort.is_prop u || Sort.is_sprop u)
  end. *)

Ltac cong := intuition congruence.

Lemma leq_relevance_eq {cf φ} {s s'} :
  leq_sort φ s s' -> relevance_of_sort s = relevance_of_sort s'.
Proof.
  now destruct s, s'.
Qed.

Lemma leq_relevance_opt {cf φ} {s s' rel} :
  leq_sort φ s s' -> isSortRelOpt s rel -> isSortRelOpt s' rel.
Proof.
  now destruct s, s'.
Qed.

Lemma leq_relevance {cf φ} {s s' rel} :
  leq_sort φ s s' -> isSortRel s rel -> isSortRel s' rel.
Proof.
  now destruct s, s'.
Qed.

Lemma geq_relevance {cf φ} {s s' rel} :
  leq_sort φ s' s -> isSortRel s rel -> isSortRel s' rel.
Proof.
  now destruct s, s'.
Qed.

Lemma relevance_super s : relevance_of_sort (Sort.super s) = rel_of_Type.
Proof using Type.
  now destruct s.
Qed.

Lemma leq_sort_product_mon {cf} ϕ s1 s1' s2 s2' :
  leq_sort ϕ s1 s1' ->
  leq_sort ϕ s2 s2' ->
  leq_sort ϕ (Sort.sort_of_product s1 s2) (Sort.sort_of_product s1' s2').
Proof.
  destruct s2 as [| | u2], s2' as [| | u2']; cbnr; try absurd;
  destruct s1 as [| | u1], s1' as [| | u1']; cbnr; try absurd; trivial.
  - intros _ H2; etransitivity; [apply H2 | apply leq_universe_sup_r].
  - apply leq_universe_sup_mon.
Qed.

Lemma impredicative_product {cf} {ϕ l u} :
  Sort.is_propositional u ->
  leq_sort ϕ (Sort.sort_of_product l u) u.
Proof.
  destruct u => //; reflexivity.
Qed.

Section UniverseLemmas.
  Context {cf: checker_flags}.

  Lemma univ_sup_idem s : Universe.sup s s = s.
  Proof using Type.
    apply eq_univ'; cbn.
    intro; rewrite !LevelExprSet.union_spec. intuition.
  Qed.

  Lemma sup_idem s : Sort.sup s s = s.
  Proof using Type.
    destruct s; cbn; auto.
    apply f_equal.
    apply univ_sup_idem.
  Qed.

  Lemma sort_of_product_idem s
    : Sort.sort_of_product s s = s.
  Proof using Type.
    unfold Sort.sort_of_product; destruct s; try reflexivity.
    apply sup_idem.
  Qed.

  Lemma univ_sup_assoc s1 s2 s3 :
    Universe.sup s1 (Universe.sup s2 s3) = Universe.sup (Universe.sup s1 s2) s3.
  Proof using Type.
    apply eq_univ'; cbn. symmetry; apply LevelExprSetProp.union_assoc.
  Qed.

  Instance proper_univ_sup_eq_univ φ :
    Proper (eq_universe φ ==> eq_universe φ ==> eq_universe φ) Universe.sup.
  Proof using Type.
    intros u1 u1' H1 u2 u2' H2.
    unfold_univ_rel.
    rewrite !val_sup. lia.
  Qed.

  Instance proper_sort_sup_eq_sort φ :
    Proper (eq_sort φ ==> eq_sort φ ==> eq_sort φ) Sort.sup.
  Proof using Type.
    intros [| | u1] [| |u1'] H1 [| |u2] [| |u2'] H2; cbn in *; try absurd; auto.
    now apply proper_univ_sup_eq_univ.
  Qed.

  Lemma sort_of_product_twice u s :
    Sort.sort_of_product u (Sort.sort_of_product u s)
    = Sort.sort_of_product u s.
  Proof using Type.
    destruct u,s; cbnr.
    now rewrite univ_sup_assoc univ_sup_idem.
  Qed.
End UniverseLemmas.


Section no_prop_leq_type.
  Context {cf: checker_flags}.
  Context (ϕ : ConstraintSet.t).

  Lemma succ_inj x y : LevelExpr.succ x = LevelExpr.succ y -> x = y.
  Proof using Type.
    unfold LevelExpr.succ.
    destruct x as [l n], y as [l' n']. simpl. congruence.
  Qed.

  Lemma spec_map_succ l x :
    LevelExprSet.In x (Universe.succ l) <->
    exists x', LevelExprSet.In x' l /\ x = LevelExpr.succ x'.
  Proof using Type.
    rewrite map_spec. reflexivity.
  Qed.

  Lemma val_succ v l : val v (LevelExpr.succ l) = val v l + 1.
  Proof using Type.
    destruct l as []; simpl. cbn. lia.
  Qed.

  Lemma val_map_succ v l : val v (Universe.succ l) = val v l + 1.
  Proof using Type.
    pose proof (spec_map_succ l).
    set (n := Universe.succ l) in *.
    destruct (val_In_max l v) as [max [inmax eqv]]. rewrite <-eqv.
    rewrite val_caract. split.
    intros.
    specialize (proj1 (H _) H0) as [x' [inx' eq]]. subst e.
    rewrite val_succ. eapply (val_In_le _ v) in inx'. rewrite <- eqv in inx'.
    simpl in *. unfold LevelExprSet.elt, LevelExpr.t in *. lia.
    exists (LevelExpr.succ max). split. apply H.
    exists max; split; auto.
    now rewrite val_succ.
  Qed.

  Lemma leq_sort_super s s' :
    leq_sort ϕ s s' ->
    leq_sort ϕ (Sort.super s) (Sort.super s').
  Proof using Type.
    destruct s as [| | u1], s' as [| | u1']; cbnr; try absurd;
    intros H; unfold_univ_rel;
    rewrite !val_map_succ; lia.
  Qed.

  Lemma leq_sort_prop_no_prop_sub_type s1 s2 :
    prop_sub_type = false ->
    leq_sort ϕ s1 s2 ->
    Sort.is_prop s1 -> Sort.is_prop s2.
  Proof using Type.
    intros ps.
    destruct s1; cbn; [ | absurd | absurd].
    rewrite ps.
    destruct s2; cbn; [ auto | absurd | absurd].
  Qed.

  Hint Resolve leq_sort_prop_no_prop_sub_type : univ_lemmas.

  Lemma leq_prop_is_propositonal {s1 s2} :
    prop_sub_type = false ->
    leq_sort ϕ s1 s2 ->
    Sort.is_propositional s1 <-> Sort.is_propositional s2.
  Proof using Type.
    intros ps.
    destruct s1, s2; cbn; try absurd; intros H; split; trivial.
    now rewrite ps in H.
  Qed.


End no_prop_leq_type.


(* This level is a hack used in plugings to generate fresh levels *)
Definition fresh_level : Level.t := Level.level     "__metarocq_fresh_level__".
(* This universe is a hack used in plugins to generate fresh universes *)
Definition fresh_universe : Universe.t := Universe.make' fresh_level.

(** * Universe substitution

  Substitution of universe levels for universe level lvariables, used to
  implement universe polymorphism. *)


(** Substitutable type *)

Class UnivSubst A := subst_instance : Instance.t -> A -> A.

Notation "x @[ u ]" := (subst_instance u x) (at level 3,
  format "x @[ u ]").

#[global] Instance subst_instance_level : UnivSubst Level.t :=
  fun u l => match l with
            Level.lzero | Level.level     _ => l
          | Level.lvar n => List.nth n u Level.lzero
          end.

#[global] Instance subst_instance_level_expr : UnivSubst LevelExpr.t :=
fun u e => match e with
        | (Level.lzero, _)
        | (Level.level _, _) => e
        | (Level.lvar n, b) =>
          match nth_error u n with
          | Some l => (l,b)
          | None => (Level.lzero, b)
          end
        end.

#[global] Instance subst_instance_universe : UnivSubst Universe.t :=
  fun u => map (subst_instance_level_expr u).

#[global] Instance subst_instance_cstr : UnivSubst LevelConstraint.t :=
  fun u c => (subst_instance_level u c.1.1, c.1.2, subst_instance_level u c.2).

#[global] Instance subst_instance_univ_cstr : UnivSubst UnivConstraint.t :=
  fun u c => (subst_instance u c.1.1, c.1.2, subst_instance u c.2).

#[global] Instance subst_instance_cstrs : UnivSubst ConstraintSet.t :=
  fun u ctrs => ConstraintSet.fold (fun c => ConstraintSet.add (subst_instance_cstr u c))
                                ctrs ConstraintSet.empty.

#[global] Instance subst_instance_sort : UnivSubst Sort.t :=
  fun u e => match e with
          | sProp | sSProp => e
          | sType u' => sType (subst_instance u u')
          end.

Lemma subst_instance_to_family s u :
  Sort.to_family s@[u] = Sort.to_family s.
Proof.
  destruct s => //.
Qed.

#[global] Instance subst_instance_instance : UnivSubst Instance.t :=
  fun u u' => List.map (subst_instance_level u) u'.


Theorem relevance_subst_eq u s : relevance_of_sort (subst_instance_sort u s) = relevance_of_sort s.
Proof.
  now destruct s.
Qed.

Theorem relevance_subst_opt u rel s :
  isSortRelOpt s rel -> isSortRelOpt (subst_instance_sort u s) rel.
Proof.
  now destruct s.
Qed.

Theorem relevance_subst u rel s :
  isSortRel s rel -> isSortRel (subst_instance_sort u s) rel.
Proof.
  now destruct s.
Qed.


(** Tests that the term is closed over [k] universe variables *)
Section Closedu.
  Context (k : nat).

  Definition closedu_level (l : Level.t) :=
    match l with
    | Level.lvar n => (n <? k)%nat
    | _ => true
    end.

  Definition closedu_level_expr (s : LevelExpr.t) :=
    closedu_level (LevelExpr.get_level s).

  Definition closedu_universe (u : Universe.t) :=
    LevelExprSet.for_all closedu_level_expr u.

  Definition closedu_sort (u : Sort.t) :=
    match u with
    | sSProp | sProp => true
    | sType l => closedu_universe l
    end.

  Definition closedu_instance (u : Instance.t) :=
    forallb closedu_level u.
End Closedu.

(** Universe-closed terms are unaffected by universe substitution. *)
Section UniverseClosedSubst.
  Lemma closedu_subst_instance_level u l
  : closedu_level 0 l -> subst_instance_level u l = l.
  Proof.
    destruct l; cbnr. discriminate.
  Qed.

  Lemma closedu_subst_instance_level_expr u e
    : closedu_level_expr 0 e -> subst_instance_level_expr u e = e.
  Proof.
    intros.
    destruct e as [t b]. destruct t;cbnr. discriminate.
  Qed.

  Lemma closedu_subst_instance_univ u s
    : closedu_sort 0 s -> subst_instance_sort u s = s.
  Proof.
    intro H.
    destruct s as [| | t]; cbnr.
    apply f_equal. apply eq_univ'.
    destruct t as [ts H1].
    unfold closedu_universe in *;cbn in *.
    intro e; split; intro He.
    - apply map_spec in He. destruct He as [e' [He' X]].
      rewrite closedu_subst_instance_level_expr in X.
      apply LevelExprSet.for_all_spec in H; proper.
      exact (H _ He').
      now subst.
    - apply map_spec. exists e; split; tas.
      symmetry; apply closedu_subst_instance_level_expr.
      apply LevelExprSet.for_all_spec in H; proper. now apply H.
  Qed.

  Lemma closedu_subst_instance u t
    : closedu_instance 0 t -> subst_instance u t = t.
  Proof.
    intro H. apply forall_map_id_spec.
    apply Forall_forall; intros l Hl.
    apply closedu_subst_instance_level.
    eapply forallb_forall in H; eassumption.
  Qed.

End UniverseClosedSubst.

#[global]
Hint Resolve closedu_subst_instance_level closedu_subst_instance_level_expr
     closedu_subst_instance_univ closedu_subst_instance : substu.

(** Substitution of a universe-closed instance of the right size
    produces a universe-closed term. *)
Section SubstInstanceClosed.
  Context (u : Instance.t) (Hcl : closedu_instance 0 u).

  Lemma subst_instance_level_closedu l
    : closedu_level #|u| l -> closedu_level 0 (subst_instance_level u l).
  Proof using Hcl.
    destruct l; cbnr.
    unfold closedu_instance in Hcl.
    destruct (nth_in_or_default n u Level.lzero).
    - intros _. eapply forallb_forall in Hcl; tea.
    - rewrite e; reflexivity.
  Qed.

  Lemma subst_instance_level_expr_closedu e :
    closedu_level_expr #|u| e -> closedu_level_expr 0 (subst_instance_level_expr u e).
  Proof using Hcl.
    destruct e as [l b]. destruct l;cbnr.
    case_eq (nth_error u n); cbnr. intros [] Hl X; cbnr.
    apply nth_error_In in Hl.
    eapply forallb_forall in Hcl; tea.
    discriminate.
  Qed.

  Lemma subst_instance_univ_closedu s
    : closedu_sort #|u| s -> closedu_sort 0 (subst_instance_sort u s).
  Proof using Hcl.
    intro H.
    destruct s as [| |t]; cbnr.
    destruct t as [l Hl].
    apply LevelExprSet.for_all_spec; proper.
    intros e He. eapply map_spec in He.
    destruct He as [e' [He' X]]; subst.
    apply subst_instance_level_expr_closedu.
    apply LevelExprSet.for_all_spec in H; proper.
    now apply H.
  Qed.

  Lemma subst_instance_closedu t :
    closedu_instance #|u| t -> closedu_instance 0 (subst_instance u t).
  Proof using Hcl.
    intro H. etransitivity. eapply forallb_map.
    eapply forallb_impl; tea.
    intros l Hl; cbn. apply subst_instance_level_closedu.
  Qed.
End SubstInstanceClosed.

#[global]
Hint Resolve subst_instance_level_closedu subst_instance_level_expr_closedu
     subst_instance_univ_closedu subst_instance_closedu : substu.


Definition string_of_level (l : Level.t) : string :=
  match l with
  | Level.lzero => "Set"
  | Level.level     s => s
  | Level.lvar n => "lvar" ^ string_of_nat n
  end.

Definition string_of_level_expr (e : LevelExpr.t) : string :=
  let '(l, n) := e in string_of_level l ^ (if n is 0 then "" else "+" ^ string_of_nat n).

Definition string_of_universe (e : LevelExprSet.t) : string :=
  string_of_list string_of_level_expr (LevelExprSet.elements e).

Definition string_of_sort (u : Sort.t) :=
  match u with
  | Sort.sSProp => "SProp"
  | Sort.sProp => "Prop"
  | Sort.sType l => "Type(" ^ string_of_universe l ^ ")"
  end.

Definition string_of_universe_instance u :=
  string_of_list string_of_level u.

Inductive universes_entry :=
| Monomorphic_entry (ctx : ContextSet.t)
| Polymorphic_entry (ctx : UContext.t).
Derive NoConfusion for universes_entry.

Definition universes_entry_of_decl (u : universes_decl) : universes_entry :=
  match u with
  | Polymorphic_ctx ctx => Polymorphic_entry (Universes.AUContext.repr ctx)
  | Monomorphic_ctx => Monomorphic_entry ContextSet.empty
  end.

Definition polymorphic_instance uctx :=
  match uctx with
  | Monomorphic_ctx => Instance.empty
  | Polymorphic_ctx c => fst (snd (AUContext.repr c))
  end.
(* TODO: duplicate of polymorphic_instance *)
Definition abstract_instance decl :=
  match decl with
  | Monomorphic_ctx => Instance.empty
  | Polymorphic_ctx auctx => UContext.instance (AUContext.repr auctx)
  end.

Definition print_universe_instance u :=
  match u with
  | [] => ""
  | _ => "@{" ^ print_list string_of_level " " u ^ "}"
  end.

Definition print_lset t :=
  print_list string_of_level " " (LevelSet.elements t).

Definition print_constraint_type d :=
  match d with
  | ConstraintType.Le n =>
    if (n =? 0)%Z then "<=" else
    if (n =? 1)%Z then "<" else
    if (n <? 0)%Z then "<=" ^ string_of_nat (Z.to_nat (Z.abs n)) ^ " + "
    else " + " ^ string_of_nat (Z.to_nat n) ^ " <= "
  | ConstraintType.Eq => "="
  end.

Definition print_level_constraint '(l1, d, l2) :=
  string_of_level l1 ^ " " ^
  print_constraint_type d ^ " " ^ string_of_level l2.

Definition print_level_constraint_set t :=
  print_list print_level_constraint
    " /\ " (ConstraintSet.elements t).

Definition print_univ_constraint '(l1, d, l2) :=
  string_of_universe (l1 : Universe.t) ^ " " ^
  print_constraint_type d ^ " " ^ string_of_universe (l2 : Universe.t).

Definition print_univ_constraint_set t :=
  print_list print_univ_constraint " /\ " (UnivConstraintSet.elements t).
