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

  Definition succ (l : t) := (fst l, S (snd l)).

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

Module LevelExprSet := MSetList.MakeWithLeibniz LevelExpr.
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



Record nonEmptyLevelExprSet
  := { t_set : LevelExprSet.t ;
       t_ne  : LevelExprSet.is_empty t_set = false }.

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


Module UnivLvl.
  (** A universe level / an algebraic expression is a list of level expressions which is:
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

  Global Instance Evaluable : Evaluable UnivLvl.t
    := fun v u =>
      let '(e, u) := UnivLvl.exprs u in
      List.fold_left (fun n e => Nat.max (val v e) n) u (val v e).

  (** Test if the universe is a lub of levels or contains +n's. *)
  Definition is_levels (u : t) : bool :=
    LevelExprSet.for_all LevelExpr.is_level u.

  (** Test if the universe is a level or an algebraic universe. *)
  Definition is_level (u : t) : bool :=
    (LevelExprSet.cardinal u =? 1)%nat && is_levels u.

  (* Used for quoting. *)
  Definition from_kernel_repr (e : Level.t * nat) (es : list (Level.t * nat)) : t
    := add_list es (UnivLvl.make e).

  Definition succ : t -> t := map LevelExpr.succ.

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

  Definition type0 : t := make LevelExpr.set.
  Definition type1 : t := make LevelExpr.type1.

  Lemma equal_exprsets (u v : t) : LevelExprSet.Equal u v <-> u = v.
  Proof.
    split; intro H. now apply eq_univ, LevelExprSet.eq_leibniz.
    now subst.
  Qed.

  Lemma elim :
    forall [P : t -> Type],
      (forall le, P (singleton le)) ->
      (forall le u, P u -> ~ LevelExprSet.In le u -> P (add le u)) ->
    forall u , P u.
  Proof.
    intros ? hs ha [].
    revert t_set0 t_ne0.
    apply: LevelExprSetProp.set_induction.
    - move => s /LevelExprSetFact.is_empty_1 he ne; exfalso => //. congruence.
    - intros s s' IH x nin hadd hne.
      destruct (LevelExprSet.is_empty s) eqn:hem in |- .
      + assert (singleton x = {| t_set := s'; t_ne := hne |}) as <- => //.
        unfold singleton; apply equal_exprsets; cbn.
        intro a; specialize (hadd a); rewrite hadd.
        rewrite LevelExprSet.singleton_spec; intuition.
        exfalso. apply LevelExprSetFact.is_empty_2 in hem; eapply hem; eauto.
      + specialize (IH hem). specialize (ha x _ IH).
        (* [assert] rather than ssreflect's [have]: the latter inserts the
           opaque sort-polymorphic [ssr_have_upoly], which breaks extraction
           on Rocq <= 9.2 (rocq-prover/rocq#22342). *)
        assert (e : LevelExprSet.Equal
          (add x {| t_set := s; t_ne := hem |})
          ({| t_set := s'; t_ne := hne |})).
        2: by apply equal_exprsets in e; now rewrite -e.
        intros x'; specialize (hadd x'). rewrite LevelExprSet.add_spec; cbn; intuition.
  Defined.
End UnivLvl.

Ltac u :=
  change LevelSet.elt with Level.t in *;
  change LevelExprSet.elt with LevelExpr.t in *.
  (* change ConstraintSet.elt with UnivConstraint.t in *. *)


Lemma val_fold_right (u : UnivLvl.t) v :
  val v u = fold_right (fun e x => Nat.max (val v e) x) (val v (UnivLvl.exprs u).1)
                       (List.rev (UnivLvl.exprs u).2).
Proof.
  unfold val at 1, UnivLvl.Evaluable.
  destruct (UnivLvl.exprs u).
  now rewrite fold_left_rev_right.
Qed.

Lemma val_In_le (u : UnivLvl.t) v e :
  LevelExprSet.In e u -> val v e <= val v u.
Proof.
  intro H. rewrite val_fold_right.
  apply In_to_nonempty_list_rev in H.
  fold UnivLvl.exprs in H; destruct (UnivLvl.exprs u); cbn in *.
  destruct H as [H|H].
  - subst. induction (List.rev l); cbnr. lia.
  - induction (List.rev l); cbn; invs H.
    + u; lia.
    + specialize (IHl0 H0). lia.
Qed.

Lemma val_In_max (u : UnivLvl.t) v :
  exists e, LevelExprSet.In e u /\ val v e = val v u.
Proof.
  eapply iff_ex. {
    intro. eapply and_iff_compat_r. apply In_to_nonempty_list_rev. }
  rewrite val_fold_right. fold UnivLvl.exprs; destruct (UnivLvl.exprs u) as [e l]; cbn in *.
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

Lemma val_ge_caract (u : UnivLvl.t) v k :
  (forall e, LevelExprSet.In e u -> val v e <= k) <-> val v u <= k.
Proof.
  split.
  - eapply imp_iff_compat_r. {
      eapply iff_forall; intro. eapply imp_iff_compat_r.
      apply In_to_nonempty_list_rev. }
    rewrite val_fold_right.
    fold UnivLvl.exprs; destruct (UnivLvl.exprs u) as [e l]; cbn; clear.
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

Lemma val_le_caract (u : UnivLvl.t) v k :
  (exists e, LevelExprSet.In e u /\ k <= val v e) <-> k <= val v u.
Proof.
  split.
  - eapply imp_iff_compat_r. {
      eapply iff_ex; intro. eapply and_iff_compat_r. apply In_to_nonempty_list_rev. }
    rewrite val_fold_right.
    fold UnivLvl.exprs; destruct (UnivLvl.exprs u) as [e l]; cbn; clear.
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



Lemma val_caract (u : UnivLvl.t) v k :
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

Lemma val_add v e (s: UnivLvl.t)
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
  val v (UnivLvl.sup s1 s2) = Nat.max (val v s1) (val v s2).
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


Lemma ulvl_get_is_level_correct u l :
  UnivLvl.get_is_level u = Some l -> u = UnivLvl.make' l.
Proof.
  intro H.
  unfold UnivLvl.get_is_level in *.
  destruct (LevelExprSet.elements u) as [|l0 L] eqn:Hu1; [discriminate |].
  destruct l0, L; try discriminate.
  * destruct n; inversion H; subst.
    apply eq_univ''; apply Hu1.
  * destruct n; discriminate.
Qed.

Lemma sup0_comm x1 x2 :
  UnivLvl.sup x1 x2 = UnivLvl.sup x2 x1.
Proof.
  apply eq_univ'; simpl. unfold LevelExprSet.Equal.
  intros H. rewrite !LevelExprSet.union_spec. intuition.
Qed.

Lemma ulvl_sup_idem l : UnivLvl.sup l l = l.
Proof.
  apply UnivLvl.equal_exprsets; intro le.
  rewrite LevelExprSet.union_spec; intuition.
Qed.

Lemma ulvl_sup_assoc l1 l2 l3 :
  UnivLvl.sup l1 (UnivLvl.sup l2 l3) =
    UnivLvl.sup (UnivLvl.sup l1 l2) l3.
Proof.
  apply UnivLvl.equal_exprsets; intros le.
  rewrite !LevelExprSet.union_spec; firstorder.
Qed.

(*
Lemma val_zero_exprs v (l : UnivLvl.t) : 0 <= val v l.
Proof.
  rewrite val_fold_right.
  destruct (UnivLvl.exprs l) as [e u']; clear l; cbn.
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
  Definition t : Set := Level.t * ConstraintType.t * Level.t.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition make l1 ct l2 : t := (l1, ct, l2).

  Inductive lt_ : t -> t -> Prop :=
  | lt_Level2 l1 t l2 l2' : Level.lt l2 l2' -> lt_ (l1, t, l2) (l1, t, l2')
  | lt_Cstr l1 t t' l2 l2' : ConstraintType.lt t t' -> lt_ (l1, t, l2) (l1, t', l2')
  | lt_Level1 l1 l1' t t' l2 l2' : Level.lt l1 l1' -> lt_ (l1, t, l2) (l1', t', l2').
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
End UnivConstraint.

Module ConstraintSet := MSetAVL.Make UnivConstraint.
Module ConstraintSetFact := WFactsOn UnivConstraint ConstraintSet.
Module ConstraintSetOrdProp := MSetProperties.OrdProperties ConstraintSet.
Module ConstraintSetProp := ConstraintSetOrdProp.P.
Module CS := ConstraintSet.
Module ConstraintSetDecide := ConstraintSetProp.Dec.
Module ConstraintSetExtraOrdProp := MSets.ExtraOrdProperties ConstraintSet ConstraintSetOrdProp.
Module ConstraintSetExtraDecide := MSetAVL.Decide UnivConstraint ConstraintSet.
Ltac csets := ConstraintSetDecide.fsetdec.

Notation "(=_cset)" := ConstraintSet.Equal (at level 0).
Infix "=_cset" := ConstraintSet.Equal (at level 30).
Notation "(==_cset)" := ConstraintSet.equal (at level 0).
Infix "==_cset" := ConstraintSet.equal (at level 30).

Definition declared_cstr_levels levels (cstr : UnivConstraint.t) :=
  let '(l1,_,l2) := cstr in
  LevelSet.In l1 levels /\ LevelSet.In l2 levels.

Definition is_declared_cstr_levels levels (cstr : UnivConstraint.t) : bool :=
  let '(l1,_,l2) := cstr in
  LevelSet.mem l1 levels && LevelSet.mem l2 levels.

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

Inductive ulvls_decl : Type :=
| Monomorphic_ctx
| Polymorphic_ctx (cst : AUContext.t).

Derive NoConfusion for ulvls_decl.

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

Inductive satisfies0 (v : valuation) : UnivConstraint.t -> Prop :=
| satisfies0_Lt (l l' : Level.t) (z : Z) : (Z.of_nat (val v l) <= Z.of_nat (val v l') - z)%Z
                        -> satisfies0 v (l, ConstraintType.Le z, l')
| satisfies0_Eq (l l' : Level.t) : val v l = val v l'
                        -> satisfies0 v (l, ConstraintType.Eq, l').

Definition satisfies v : ConstraintSet.t -> Prop :=
  ConstraintSet.For_all (satisfies0 v).

Lemma satisfies_union v φ1 φ2 :
  satisfies v (CS.union φ1 φ2)
  <-> (satisfies v φ1 /\ satisfies v φ2).
Proof using Type.
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
Proof using Type.
  move=> v hv; exists v; split; [move=> ? /CS.empty_spec[]| move=> ??//].
Qed.

Lemma consistent_extension_on_union X cstrs
  (wfX : forall c, CS.In c X.2 -> LS.In c.1.1 X.1 /\ LS.In c.2 X.1) :
  consistent_extension_on X cstrs <->
  consistent_extension_on X (CS.union cstrs X.2).
Proof using Type.
  split.
  2: move=> h v /h [v' [/satisfies_union [??] eqv']]; exists v'; split=> //.
  move=> hext v /[dup] vsat /hext [v' [v'sat v'eq]].
  exists v'; split=> //.
  apply/satisfies_union; split=> //.
  move=> c hc. destruct (wfX c hc).
  destruct (vsat c hc); constructor; rewrite -!v'eq //.
Qed.

Definition leq0_ulvl_n n φ (u u' : UnivLvl.t) :=
  forall v, satisfies v φ -> (Z.of_nat (val v u) <= Z.of_nat (val v u') - n)%Z.

Definition leq_ulvl_n {cf} n φ (u u' : UnivLvl.t) :=
  if check_univs then leq0_ulvl_n n φ u u' else True.

Definition lt_ulvl {cf} := leq_ulvl_n 1.
Definition leq_ulvl {cf} := leq_ulvl_n 0.

Definition eq0_ulvl φ (u u' : UnivLvl.t) :=
  forall v, satisfies v φ -> val v u = val v u'.

Definition eq_ulvl {cf} φ (u u' : UnivLvl.t) :=
  if check_univs then eq0_ulvl φ u u' else True.

(* ctrs are "enforced" by φ *)

Definition valid_constraints0 φ ctrs
  := forall v, satisfies v φ -> satisfies v ctrs.

Definition valid_constraints {cf} φ ctrs
  := if check_univs then valid_constraints0 φ ctrs else True.

Definition compare_ulvl {cf} φ (pb : conv_pb) :=
  match pb with
  | Conv => eq_ulvl φ
  | Cumul => leq_ulvl φ
  end.

Ltac unfold_ulvl_rel0 :=
  unfold eq0_ulvl, leq0_ulvl_n, valid_constraints0 in *;
  try (
    match goal with |- forall v : valuation, _ -> _ => idtac end;
    intros v Hv;
    repeat match goal with H : forall v : valuation, _ -> _ |- _ => specialize (H v Hv) end;
    cbnr
  ).

Ltac unfold_ulvl_rel :=
  unfold eq_ulvl, leq_ulvl, lt_ulvl, leq_ulvl_n, valid_constraints in *;
  destruct check_univs; [unfold_ulvl_rel0 | trivial].

Section UniverseLevel.
  Context {cf}.

  Lemma valid_subset φ φ' ctrs
    : ConstraintSet.Subset φ φ' -> valid_constraints φ ctrs
      ->  valid_constraints φ' ctrs.
  Proof using Type.
    unfold_ulvl_rel.
    intros Hφ H v Hv. apply H.
    intros ctr Hc. apply Hv. now apply Hφ.
  Qed.

  Lemma switch_minus (x y z : Z) : (x <= y - z <-> x + z <= y)%Z.
  Proof using Type. split; lia. Qed.

  (** **** Lemmas about eq and leq **** *)

  Global Instance eq_ulvl_refl φ : Reflexive (eq_ulvl φ).
  Proof using Type.
    intros u; unfold_ulvl_rel.
  Qed.

  Global Instance leq_ulvl_refl φ : Reflexive (leq_ulvl φ).
  Proof using Type.
    intros u; unfold_ulvl_rel. lia.
  Qed.

  Global Instance eq_ulvl_sym φ : Symmetric (eq_ulvl φ).
  Proof using Type.
    intros u u' H; unfold_ulvl_rel.
    lia.
  Qed.

  Global Instance eq_ulvl_trans φ : Transitive (eq_ulvl φ).
  Proof using Type.
    intros u u' u'' H1 H2; unfold_ulvl_rel.
    lia.
  Qed.

  Global Instance leq_ulvl_n_trans n φ : Transitive (leq_ulvl_n (Z.of_nat n) φ).
  Proof using Type.
    intros u u' u'' H1 H2; unfold_ulvl_rel.
    lia.
  Qed.

  Global Instance leq_ulvl_trans φ : Transitive (leq_ulvl φ).
  Proof using Type. apply (leq_ulvl_n_trans 0). Qed.

  Global Instance lt_ulvl_trans φ : Transitive (lt_ulvl φ).
  Proof using Type. apply (leq_ulvl_n_trans 1). Qed.

  Lemma eq0_leq0_ulvl φ u u' :
    eq0_ulvl φ u u' <-> leq0_ulvl_n 0 φ u u' /\ leq0_ulvl_n 0 φ u' u.
  Proof using Type.
    split.
    - intros H. split; unfold_ulvl_rel0; lia.
    - intros [H1 H2]. unfold_ulvl_rel0; lia.
  Qed.

  Lemma eq_ulvl_leq_ulvl φ u u' :
    eq_ulvl φ u u' <-> leq_ulvl φ u u' /\ leq_ulvl φ u' u.
  Proof using Type.
    unfold_ulvl_rel => //.
    apply eq0_leq0_ulvl.
  Qed.

  Lemma leq_ulvl_sup_l φ u1 u2 : leq_ulvl φ u1 (UnivLvl.sup u1 u2).
  Proof using Type. unfold_ulvl_rel. rewrite val_sup; lia. Qed.

  Lemma leq_ulvl_sup_r φ u1 u2 : leq_ulvl φ u2 (UnivLvl.sup u1 u2).
  Proof using Type. unfold_ulvl_rel. rewrite val_sup; lia. Qed.

  Lemma leq_universe_sup_mon φ u1 u1' u2 u2' : leq_ulvl φ u1 u1' -> leq_ulvl φ u2 u2' ->
    leq_ulvl φ (UnivLvl.sup u1 u2) (UnivLvl.sup u1' u2').
  Proof using Type.
    intros H1 H2; unfold_ulvl_rel.
    rewrite !val_sup. lia.
  Qed.

  Global Instance eq_leq_ulvl φ : subrelation (eq_ulvl φ) (leq_ulvl φ).
  Proof using Type.
    intros u u'. apply eq_ulvl_leq_ulvl.
  Qed.

  Global Instance eq_ulvl_equivalence φ : Equivalence (eq_ulvl φ) := Build_Equivalence _ _ _ _.

  Global Instance leq_ulvl_preorder φ : PreOrder (leq_ulvl φ) := Build_PreOrder _ _ _.

  Global Instance lt_ulvl_irrefl {c: check_univs} φ (H: consistent φ) : Irreflexive (lt_ulvl φ).
  Proof using Type.
    intro u. unfold complement.
    unfold_ulvl_rel => //.
    destruct H as [v Hv]; intros nH; specialize (nH v Hv); lia.
  Qed.

  Global Instance lt_ulvl_str_order {c: check_univs} φ (H: consistent φ) : StrictOrder (lt_ulvl φ).
  Proof.
    refine (Build_StrictOrder _ _ _).
    now unshelve eapply lt_ulvl_irrefl.
  Qed.

  Global Instance leq_ulvl_antisym φ : Antisymmetric _ (eq_ulvl φ) (leq_ulvl φ).
  Proof using Type. intros t u tu ut. now apply eq_ulvl_leq_ulvl. Qed.

  Global Instance leq_ulvl_partial_order φ
    : PartialOrder (eq_ulvl φ) (leq_ulvl φ).
  Proof.
    intros x y; split; apply eq_ulvl_leq_ulvl.
  Defined.


  Global Instance compare_ulvl_subrel φ pb : subrelation (eq_ulvl φ) (compare_ulvl φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_ulvl_refl φ pb : Reflexive (compare_ulvl φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_ulvl_trans φ pb : Transitive (compare_ulvl φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_ulvl_preorder φ pb : PreOrder (compare_ulvl φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Definition eq_leq_ulvl' φ u u'
    := @eq_leq_ulvl φ u u'.
  Definition leq_ulvl_refl' φ u
    := @leq_ulvl_refl φ u.

  Hint Resolve eq_leq_ulvl' leq_ulvl_refl' : core.

  Lemma cmp_ulvl_subset φ φ' pb t u :
    ConstraintSet.Subset φ φ' -> compare_ulvl φ pb t u -> compare_ulvl φ' pb t u.
  Proof using Type.
    intros Hctrs.
    destruct pb, t, u; cbnr; trivial.
    all: intros H; unfold_ulvl_rel;
    apply H.
    all: eapply satisfies_subset; eauto.
  Qed.

  Lemma eq_ulvl_subset φ φ' t u
    : ConstraintSet.Subset φ φ'
      -> eq_ulvl φ t u -> eq_ulvl φ' t u.
  Proof using Type. apply cmp_ulvl_subset with (pb := Conv). Qed.

  Lemma leq_universe_subset φ φ' t u
    : ConstraintSet.Subset φ φ'
      -> leq_ulvl φ t u -> leq_ulvl φ' t u.
  Proof using Type. apply cmp_ulvl_subset with (pb := Cumul). Qed.

End UniverseLevel.
