From Corelib Require Program.Tactics.
From Equations Require Import Equations.
Set Equations Transparent.
From Corelib Require Import ssreflect ssrfun ssrbool.
From Stdlib Require Import SetoidList Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import MRPrelude ReflectEq MRString MRList MRClasses SemiLattice.

Module Type OrderedTypeWithLeibniz.
  Include UsualOrderedType.
  Parameter eq_leibniz : forall (x y : t), eq x y -> x = y.
End OrderedTypeWithLeibniz.

Module Type OrderedTypeWithLeibnizWithReflect.
  Include OrderedTypeWithLeibniz.

  Parameter zero : t.
  Parameter is_global : t -> bool.
  Parameter is_global_zero : ~~ is_global zero.
  Parameter reflect_eq : ReflectEq t.
  Parameter to_string : t -> string.
End OrderedTypeWithLeibnizWithReflect.

Module Type Quantity.
  Include OrderedTypeWithLeibniz.
  Import CommutativeMonoid.

  Declare Instance comm_monoid : IsCommMonoid t.
  Declare Instance add_inj_eq n : Injective (add n) Logic.eq Logic.eq.
  Declare Instance add_inj_lt n : Injective (add n) lt lt.
End Quantity.

Module OfQuantity (Q : Quantity).
  Import CommutativeMonoid.
  Import Q.

  Declare Scope quantity.
  Bind Scope quantity with t.
  Delimit Scope quantity with Q.
  Infix "+" := add : quantity.

  Definition le (x y : t) := lt x y \/ eq x y.

  Instance le_refl : Reflexive le.
  Proof. red. now right. Qed.

  Instance le_trans : Transitive le.
  Proof. red. intros x y z [] [].
    - left. now transitivity y.
    - rewrite -H0. now left.
    - rewrite H. now left.
    - rewrite H H0. now right.
  Qed.

  Lemma add_inj_le {n} : Injective (add n) le le.
  Proof.
    intros x y []. left. now apply inj in H.
    apply inj in H. now right.
  Qed.

End OfQuantity.

Module Type LevelExprT (Level : OrderedTypeWithLeibniz) (Q : Quantity).
  Include UsualOrderedType with Definition t := (Level.t * Q.t)%type.
  Parameter eq_leibniz : forall (x y : t), eq x y -> x = y.
End LevelExprT.

Module Type LevelSet_fun (Level : UsualOrderedType).
  Include S with Module E := Level.
End LevelSet_fun.

Module Type LevelExprSet_fun (Level : OrderedTypeWithLeibniz) (Q : Quantity)
  (LevelExpr : LevelExprT Level Q).
  Include SWithLeibniz with Module E := LevelExpr.

  Parameter reflect_eq : ReflectEq t.
End LevelExprSet_fun.

Module NonEmptyLevelExprSet (Level : OrderedTypeWithLeibniz) (Q : Quantity)
  (LevelSet : LevelSet_fun Level)
  (LevelExpr : LevelExprT Level Q)
  (LevelExprSet : LevelExprSet_fun Level Q LevelExpr).
  Module LevelExprSetFact := WFactsOn LevelExpr LevelExprSet.
  Module LevelExprSetOrdProp := MSetProperties.OrdProperties LevelExprSet.
  Module LevelExprSetProp := LevelExprSetOrdProp.P.
  Module UCS := LevelExprSet.

  Module LevelSetOrdProp := MSetProperties.OrdProperties LevelSet.
  Module LevelSetProp := LevelSetOrdProp.P.
  Module LevelSetDecide := LevelSetProp.Dec.
  Ltac lsets := LevelSetDecide.fsetdec.

  Module LevelExprSetDecide := LevelExprSetProp.Dec.
  (* Module LevelExprSetExtraOrdProp := MSets.ExtraOrdProperties LevelExprSet LevelExprSetOrdProp. *)
  Module LevelExprSetExtraDecide := MSetDecide.Decide LevelExprSet.
  Ltac lesets := LevelExprSetDecide.fsetdec.

  Infix "=_lset" := LevelSet.Equal (at level 70).

  Import -(notations) LevelExprSet.
  Infix "⊂_leset" := LevelExprSet.Subset (at level 70).
  Infix "=_leset" := LevelExprSet.Equal (at level 70).

  Import CommutativeMonoid.
  Module Export OfQ := OfQuantity Q.

  Definition level : LevelExpr.t -> Level.t := fst.

  Definition levels (e : t) :=
    fold (fun le => LevelSet.add (level le)) e LevelSet.empty.

  Lemma In_elements {x} {s : LevelExprSet.t} : LevelExprSet.In x s <-> List.In x (LevelExprSet.elements s).
  Proof.
    split. now move/LevelExprSetFact.elements_1/InA_In_eq.
    now move/InA_In_eq/LevelExprSetFact.elements_2.
  Qed.

  Record t :=
    { t_set :> LevelExprSet.t ;
      t_ne : is_empty t_set = false }.

  Declare Scope nes_scope.
  Bind Scope nes_scope with t.
  Delimit Scope nes_scope with nes.
  Local Open Scope nes_scope.

  Existing Instance LevelExprSet.reflect_eq.
  Existing Instance Q.comm_monoid.
  Existing Instance Q.add_inj_eq.
  Existing Instance Q.add_inj_lt.
  Existing Instance OfQ.add_inj_le.

  (* We use uip on the is_empty condition *)
  #[export, program] Instance reflect_eq : ReflectEq t :=
    { eqb x y := eqb x.(t_set) y.(t_set) }.
  Next Obligation.
    destruct (eqb_spec (t_set x) (t_set y)); constructor.
    destruct x, y; cbn in *. subst.
    now rewrite (uip t_ne0 t_ne1).
    intros e; subst x; apply H.
    reflexivity.
  Qed.

  Lemma nis_empty s : is_empty s = false <-> ~ LevelExprSet.Empty s.
  Proof.
    destruct is_empty eqn:he; split => //.
    - apply LevelExprSet.is_empty_spec in he. contradiction.
    - intros _ he'. now eapply LevelExprSet.is_empty_spec in he'.
  Qed.

  Lemma nis_empty_exists s : is_empty s = false <-> exists le, LevelExprSet.In le s.
  Proof.
    rewrite nis_empty. split; firstorder.
    destruct (choose s) eqn:hc.
    - exists e. now apply choose_spec1 in hc.
    - apply choose_spec2 in hc. contradiction.
  Qed.

  Program Definition singleton (e : LevelExpr.t) : t
    := {| t_set := LevelExprSet.singleton e |}.
  Next Obligation.
  Proof.
    apply nis_empty => he. eapply (he e). lesets.
  Qed.

  Lemma singleton_spec {le e} : LevelExprSet.In le (singleton e) <-> le = e.
  Proof. rewrite LevelExprSet.singleton_spec. reflexivity. Qed.

  Lemma not_Empty_is_empty s :
    ~ LevelExprSet.Empty s <-> LevelExprSet.is_empty s = false.
  Proof. now rewrite nis_empty. Qed.

  Program Definition add (e : LevelExpr.t) (u : t) : t
    := {| t_set := LevelExprSet.add e u |}.
  Next Obligation.
    apply not_Empty_is_empty; intro H.
    eapply H. eapply LevelExprSet.add_spec.
    left; reflexivity.
  Qed.

  Lemma add_spec_les {le e es} : LevelExprSet.In le (add e es) <-> LevelExprSet.In le (LevelExprSet.add e es).
  Proof. reflexivity. Qed.

  Lemma add_spec e u e' :
    In e' (add e u) <-> e' = e \/ In e' u.
  Proof.
    apply LevelExprSet.add_spec.
  Qed.

  Definition add_list : list LevelExpr.t -> t -> t
    := List.fold_left (fun u e => add e u).

  Lemma add_list_spec l u e :
    LevelExprSet.In e (add_list l u) <-> List.In e l \/ LevelExprSet.In e u.
  Proof.
    unfold add_list. rewrite <- fold_left_rev_right.
    etransitivity. 2:{ eapply or_iff_compat_r. etransitivity.
                       2: apply @InA_In_eq with (A:=LevelExpr.t).
                       eapply InA_rev. }
    induction (List.rev l); cbn.
    - split. intuition. intros [H|H]; tas. depelim H.
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

  Lemma elements_not_empty {u : t} : LevelExprSet.elements u <> [].
  Proof.
    rewrite -LevelExprSetProp.elements_Empty.
    move/LevelExprSetFact.is_empty_1.
    destruct u as [u1 u2]; cbn in *. congruence.
  Qed.

  Equations to_nonempty_list (u : t) : LevelExpr.t * list LevelExpr.t :=
  | u with inspect (LevelExprSet.elements u) := {
    | exist [] eqel => False_rect _ (elements_not_empty eqel)
    | exist (e :: l) _ => (e, l) }.

  Lemma singleton_to_nonempty_list e : to_nonempty_list (singleton e) = (e, []).
  Proof.
    funelim (to_nonempty_list (singleton e)). Tactics.bang.
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
    funelim (to_nonempty_list u). Tactics.bang. now rewrite e0.
  Qed.

  Lemma to_nonempty_list_spec' u :
    (to_nonempty_list u).1 :: (to_nonempty_list u).2 = elements u.
  Proof.
    pose proof (to_nonempty_list_spec u).
    now destruct (to_nonempty_list u).
  Qed.

  Lemma In_to_nonempty_list (u : t) (e : LevelExpr.t) :
    In e u
    <-> e = (to_nonempty_list u).1 \/ List.In e (to_nonempty_list u).2.
  Proof.
    etransitivity. symmetry. apply LevelExprSet.elements_spec1.
    pose proof (to_nonempty_list_spec' u) as H.
    destruct (to_nonempty_list u) as [e' l]; cbn in *.
    rewrite <- H; clear. etransitivity. apply InA_cons.
    eapply or_iff_compat_l. apply InA_In_eq.
  Qed.

  Lemma In_to_nonempty_list_rev (u : t) (e : LevelExpr.t) :
    In e u <-> e = (to_nonempty_list u).1 \/ List.In e (List.rev (to_nonempty_list u).2).
  Proof.
    etransitivity. eapply In_to_nonempty_list.
    apply or_iff_compat_l. apply in_rev.
  Qed.

  Definition map_levelexprset f u :=
    LevelExprSetProp.of_list (List.map f (LevelExprSet.elements u)).

  Program Definition map (f : LevelExpr.t -> LevelExpr.t) (u : t) : t :=
    {| t_set := map_levelexprset f u |}.
  Next Obligation.
    rewrite /map_levelexprset.
    have hs := to_nonempty_list_spec u.
    destruct (to_nonempty_list u). rewrite -hs. cbn.
    apply not_Empty_is_empty => he. apply (he (f t0)).
    lesets.
  Qed.

  Lemma map_levelexprset_spec f u e :
    LevelExprSet.In e (map_levelexprset f u) <-> exists e0, LevelExprSet.In e0 u /\ e = (f e0).
  Proof.
    unfold map; cbn.
    rewrite LevelExprSetProp.of_list_1 InA_In_eq in_map_iff.
    split.
    - intros [x [<- hin]]. exists x. split => //.
      rewrite -InA_In_eq in hin. now apply LevelExprSet.elements_spec1 in hin.
    - intros [x [hin ->]]. exists x. split => //.
      rewrite -InA_In_eq. now apply LevelExprSet.elements_spec1.
  Qed.

  Lemma map_spec f u e :
    LevelExprSet.In e (map f u) <-> exists e0, LevelExprSet.In e0 u /\ e = (f e0).
  Proof. apply map_levelexprset_spec. Qed.

  Program Definition non_empty_union (u v : t) : t :=
    {| t_set := LevelExprSet.union u v |}.
  Next Obligation.
    apply not_Empty_is_empty; intro H.
    assert (HH: LevelExprSet.Empty u). {
      intros x Hx. apply (H x).
      eapply LevelExprSet.union_spec. now left. }
    apply LevelExprSetFact.is_empty_1 in HH.
    rewrite t_ne in HH; discriminate.
  Qed.

  Lemma eq_exprsets (u v : t) :
    u = v :> LevelExprSet.t -> u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; cbn. intros X; destruct X.
    now rewrite (uip_bool _ _ u2 v2).
  Qed.

  Definition eq_univ (u v : t) : u = v :> LevelExprSet.t -> u = v := eq_exprsets u v.

  Lemma equal_exprsets (u v : t) : LevelExprSet.Equal u v <-> u = v.
  Proof.
    split; intro H. now apply eq_univ, LevelExprSet.eq_leibniz.
    now subst.
  Qed.

  #[deprecated(note = "use equal_exprsets instead")]
  Notation eq_univ_equal := equal_exprsets.

  #[deprecated(note = "use equal_exprsets instead")]
  Notation eq_univ' := equal_exprsets.

  Lemma equal_elements (u v : t) :
    LevelExprSet.elements u = LevelExprSet.elements v -> u = v.
  Proof.
    intro H. apply eq_univ.
    destruct u as [u1 u2], v as [v1 v2]; cbn in *; clear u2 v2.
    eapply LevelExprSet.eq_leibniz. red.
    intros x. rewrite -!LevelExprSet.elements_spec1 H //.
  Qed.

  #[deprecated(note = "use equal_elements instead")]
  Notation eq_univ_elements := equal_elements.

  #[deprecated(note = "use equal_elements instead")]
  Definition eq_univ'' := equal_elements.

  Lemma univ_expr_eqb_true_iff (u v : t) :
    LevelExprSet.equal u v <-> u = v.
  Proof.
    split.
    - intros.
      apply equal_exprsets. now apply LevelExprSet.equal_spec.
    - intros ->. now apply LevelExprSet.equal_spec.
  Qed.

  Lemma univ_expr_eqb_comm (u v : t) :
    LevelExprSet.equal u v <-> LevelExprSet.equal v u.
  Proof.
    transitivity (u = v). 2: transitivity (v = u).
    - apply univ_expr_eqb_true_iff.
    - split; apply eq_sym.
    - split; apply univ_expr_eqb_true_iff.
  Qed.


  Lemma for_all_false f u :
    for_all f u = false -> exists_ (negb ∘ f) u.
  Proof.
    intro H. rewrite LevelExprSetFact.exists_b.
    rewrite LevelExprSetFact.for_all_b in H.
    all: try now intros x y [].
    induction (LevelExprSet.elements u); cbn in *; [discriminate|].
    apply andb_false_iff in H; apply orb_true_iff; destruct H as [H|H].
    left; now rewrite H.
    right; now rewrite IHl.
  Qed.

  Lemma For_all_exprs (P : LevelExpr.t -> Prop) (u : t)
    : For_all P u
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
    apply equal_exprsets. intros x.
    rewrite !LevelExprSet.add_spec. firstorder.
  Qed.

  #[program]
  Definition union (prems prems' : t) : t :=
    {| t_set := LevelExprSet.union prems prems' |}.
  Next Obligation.
    destruct prems, prems'; cbn.
    destruct (LevelExprSet.is_empty (LevelExprSet.union _ _)) eqn:ise => //.
    eapply LevelExprSetFact.is_empty_2 in ise.
    eapply not_Empty_is_empty in t_ne0, t_ne1.
    destruct t_ne0. lesets.
  Qed.

  Infix "∪" := union (at level 60): nes_scope.

  Lemma union_spec u u' l :
    LevelExprSet.In l (u ∪ u') <->
    LevelExprSet.In l u \/ LevelExprSet.In l u'.
  Proof.
    destruct u, u'; unfold union; cbn.
    apply LevelExprSet.union_spec.
  Qed.

  Lemma union_add_singleton u le : union u (singleton le) = add le u.
  Proof.
    apply equal_exprsets.
    intros x. rewrite union_spec LevelExprSet.singleton_spec add_spec.
    intuition auto.
  Qed.

  Lemma union_comm {u u'} : u ∪ u' = union u' u.
  Proof.
    apply equal_exprsets.
    intros x. rewrite !union_spec.
    intuition auto.
  Qed.

  Lemma union_add_distr {le u u'} : union (add le u) u' = add le (u ∪ u').
  Proof.
    apply equal_exprsets.
    intros x. rewrite !union_spec !add_spec !union_spec.
    intuition auto.
  Qed.

  Lemma union_idem u : union u u = u.
  Proof.
    apply equal_exprsets => l.
    rewrite union_spec. firstorder.
  Qed.

  Lemma levels_spec_aux l (e : LevelExprSet.t) acc :
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
        left. exists x.2. red in H. subst.
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

  Lemma levels_spec l (e : LevelExprSet.t) :
    LevelSet.In l (levels e) <-> exists k, LevelExprSet.In (l, k) e.
  Proof.
    rewrite levels_spec_aux. intuition auto. lsets.
  Qed.


  Lemma levelexprset_singleton {l le} : (exists k : Q.t, LevelExprSet.In (l, k) (singleton le)) <-> (l, le.2) = le.
  Proof.
    split.
    - move=> [] k. now move/LevelExprSet.singleton_spec; rewrite /E.eq => <-.
    - intros <-. now exists le.2; apply LevelExprSet.singleton_spec.
  Qed.

  Lemma levels_singleton le : levels (LevelExprSet.singleton le) =_lset LevelSet.singleton le.1.
  Proof.
    intros l; rewrite levels_spec.
    rewrite LevelSet.singleton_spec; setoid_rewrite LevelExprSet.singleton_spec.
    rewrite /E.eq /LevelSet.E.eq. firstorder. now subst. subst. exists le.2; now destruct le.
  Qed.

  Lemma levels_union {u u'} : levels (u ∪ u') =_lset LevelSet.union (levels u) (levels u').
  Proof.
    intros l; rewrite levels_spec; setoid_rewrite LevelExprSet.union_spec.
    rewrite LevelSet.union_spec !levels_spec. firstorder.
  Qed.

  Lemma levels_add {le u} : levels (add le u) =_lset LevelSet.union (LevelSet.singleton le.1) (levels u).
  Proof.
    rewrite -union_add_singleton levels_union levels_singleton; lsets.
  Qed.

  #[export] Instance proper_levels : Proper (LevelExprSet.Equal ==> LevelSet.Equal)
    levels.
  Proof.
    intros s s' eq l.
    rewrite !levels_spec.
    firstorder eauto.
  Qed.

  Definition choose (u : t) : LevelExpr.t := (to_nonempty_list u).1.

  Lemma choose_spec u : In (choose u) u.
  Proof.
    rewrite /choose.
    have hs := to_nonempty_list_spec u.
    destruct to_nonempty_list. cbn.
    rewrite -elements_spec1 InA_In_eq -hs.
    now constructor.
  Qed.

  Definition eq x y := eq (t_set x) (t_set y).

  #[export] Instance proper_choose : Proper (eq ==> Logic.eq) choose.
  Proof.
    intros x y e.
    rewrite /choose.
    have he := to_nonempty_list_spec x.
    have he' := to_nonempty_list_spec y.
    do 2 destruct to_nonempty_list. cbn. red in e.
    apply LevelExprSet.eq_leibniz in e. now subst.
  Qed.

  Lemma univ_non_empty (u : t) : ~ LevelSet.Empty (levels u).
  Proof.
    intros he.
    apply (he (choose u).1).
    rewrite levels_spec. exists (choose u).2.
    destruct (choose u) eqn:e; cbn. rewrite -e.
    apply choose_spec.
  Qed.

  Lemma elim {P : t -> Type} :
    (forall le, P (singleton le)) ->
    (forall le x, P x -> ~ LevelExprSet.In le x -> P (add le x)) ->
    forall x, P x.
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
        unfold singleton. apply equal_exprsets. cbn.
        intros a. specialize (hadd a). rewrite hadd.
        rewrite LevelExprSet.singleton_spec. firstorder. subst. reflexivity.
        specialize (IH hem).
        specialize (ha x _ IH).
        assert (LevelExprSet.Equal (add x {| t_set := s; t_ne := hem|}) {| t_set := s'; t_ne := hne |}).
        2:{ apply equal_exprsets in H. now rewrite -H. }
        intros x'. specialize (hadd x'). rewrite LevelExprSet.add_spec.
        cbn. firstorder. subst x'. now left.
  Qed.

  Lemma union_assoc {s t u} : union (s ∪ t) u =
    union s (t ∪ u).
  Proof.
    apply equal_exprsets.
    intros x. rewrite !union_spec.
    intuition auto.
  Qed.

  Lemma map_map f g x : map f (map g x) = map (f ∘ g) x.
  Proof.
    apply equal_exprsets.
    intros lk.
    rewrite !map_spec. setoid_rewrite map_spec.
    firstorder eauto. subst. firstorder.
  Qed.

  Definition add_expr n '((l, k) : LevelExpr.t) := (l, CommutativeMonoid.add n k).

  Lemma add_expr_add_expr n n' lk : add_expr n (add_expr n' lk) = add_expr (CommutativeMonoid.add n n') lk.
  Proof. destruct lk; unfold add_expr. f_equal. symmetry.
    now rewrite (MRClasses.assoc (f:=CommutativeMonoid.add)). Qed.
  Definition add_prems n s := map (add_expr n) s.

  Lemma In_add_prems k (prems : t):
    forall le, LevelExprSet.In le (add_prems k prems) <->
      exists le', LevelExprSet.In le' prems /\ le = add_expr k le'.
  Proof.
    intros [l k'].
    now rewrite /add_prems map_spec.
  Qed.

  Lemma add_expr_inj {n e e'} : add_expr n e = add_expr n e' -> e = e'.
  Proof.
    destruct e, e'; cbn; rewrite /add_expr.
    move=> [=] ->.
    now move/(inj (f:=CommutativeMonoid.add n)) => ->.
  Qed.

  Lemma add_prems_inj n prems prems' : add_prems n prems = add_prems n prems' -> prems = prems'.
  Proof.
    rewrite /add_prems => /equal_exprsets hm.
    apply equal_exprsets.
    intros [l k]. specialize (hm (l, CommutativeMonoid.add n k)).
    rewrite !map_spec in hm. destruct hm as [hl hr].
    split; intros hin.
    - forward hl. exists (l, k); split => //.
      destruct hl as [[] [hin' eq]].
      apply (@add_expr_inj n (l, k)) in eq.
       now noconf eq.
    - forward hr. exists (l, k); split => //.
      destruct hr as [[] [hin' eq]].
      apply (@add_expr_inj n (l, k)) in eq. now noconf eq.
  Qed.

  Lemma inj_add_prems_sub {n u u'} : add_prems n u ⊂_leset add_prems n u' -> u ⊂_leset u'.
  Proof.
    rewrite /add_prems.
    intros hm [l k]. specialize (hm (l, CommutativeMonoid.add n k)).
    rewrite !map_spec in hm.
    intros hin.
    forward hm. exists (l, k); split => //.
    destruct hm as [[] [hin' eq]].
    apply (@add_expr_inj n (l, k)) in eq. now noconf eq.
  Qed.

  Lemma add_prems_add_prems n n' lk : add_prems n (add_prems n' lk) = add_prems (CommutativeMonoid.add n n') lk.
  Proof. destruct lk; unfold add_prems.
    rewrite map_map. apply equal_exprsets.
    intros x. rewrite !map_spec. cbn in *.
    firstorder eauto. subst. exists x0.
    firstorder eauto. now rewrite add_expr_add_expr.
    subst. exists x0.
    firstorder eauto. now rewrite add_expr_add_expr.
  Qed.

  Lemma add_prems_add {n lk prems} : add_prems n (add lk prems) = add (add_expr n lk) (add_prems n prems).
  Proof.
    apply equal_exprsets. intros x.
    rewrite In_add_prems LevelExprSet.add_spec In_add_prems /LevelExprSet.E.eq;
      setoid_rewrite LevelExprSet.add_spec.
    firstorder. subst. red in H; subst x0. now left.
  Qed.

  Lemma add_expr_0 e : add_expr CommutativeMonoid.zero e = e.
  Proof.
    destruct e => //=. now rewrite neutral.
  Qed.

  Lemma add_prems_0 u : add_prems CommutativeMonoid.zero u = u.
  Proof.
    rewrite /add_prems.
    apply equal_exprsets.
    intros x. rewrite map_spec.
    split.
    - intros[e [hin ->]]. now rewrite add_expr_0.
    - intros inu; exists x. split => //. now rewrite add_expr_0.
  Qed.

  Lemma add_prems_union {n u u'} : add_prems n (u ∪ u') = union (add_prems n u) (add_prems n u').
  Proof.
    apply equal_exprsets => l.
    rewrite In_add_prems.
    setoid_rewrite union_spec.
    rewrite !In_add_prems. firstorder.
  Qed.

  Lemma add_idem {l x} : add l (add l x) = add l x.
  Proof.
    apply equal_exprsets => l'.
    rewrite !add_spec. firstorder.
  Qed.

  Lemma add_prems_singleton n cl : add_prems n (singleton cl) = singleton (add_expr n cl).
  Proof.
    apply equal_exprsets => [] [l k].
    rewrite In_add_prems LevelExprSet.singleton_spec.
    firstorder.
    - destruct x; noconf H0.
      eapply LevelExprSet.singleton_spec in H.
      now red in H; noconf H.
    - destruct cl. red in H. noconf H. exists (t0, t1). split => //.
      now apply LevelExprSet.singleton_spec.
  Qed.

  Definition choose_prems (u : t) : LevelExpr.t := (to_nonempty_list u).1.
  Lemma choose_prems_spec u : LevelExprSet.In (choose_prems u) u.
  Proof.
    rewrite /choose_prems.
    have hs := to_nonempty_list_spec u.
    destruct to_nonempty_list. cbn.
    rewrite -LevelExprSet.elements_spec1 InA_In_eq -hs.
    now constructor.
  Qed.

  Section SemilatticeInterp.
    Import Semilattice.
    Context {S: Type} {SL : Semilattice S Q.t}.
    Context (v : Level.t -> S).

    Definition interp_expr '(l, k) := (add k (v l)).

    Definition interp_prems prems :=
      let '(hd, tl) := to_nonempty_list prems in
      fold_right (fun lk acc => join (interp_expr lk) acc) (interp_expr hd) tl.

    Lemma interp_add_expr n e :
      interp_expr (add_expr n e) ≡ add n (interp_expr e).
    Proof.
      destruct e as [l k]; cbn. now rewrite add_distr.
    Qed.

    Lemma interp_prems_singleton e :
      interp_prems (singleton e) = interp_expr e.
    Proof.
      rewrite /interp_prems.
      now rewrite singleton_to_nonempty_list /=.
    Qed.

    Lemma interp_prems_ge (prems : t) :
      forall prem, LevelExprSet.In prem prems ->
      interp_expr prem ≤ interp_prems prems.
    Proof.
      intros.
      unfold interp_prems.
      have he := to_nonempty_list_spec prems.
      destruct to_nonempty_list.
      pose proof to_nonempty_list_spec'.
      rewrite In_elements in H. rewrite -he in H. clear H0 he. clear -H.
      destruct H. subst t0.
      - induction l. cbn. auto.
        cbn. red. eapply join_idem. cbn.
        etransitivity; tea.
        apply join_le_right.
      - induction l in H |- *.
        now cbn in H.
        cbn in H. destruct H; subst; cbn.
        * cbn. apply join_le_left.
        * specialize (IHl H). etransitivity; tea. apply join_le_right.
    Qed.

    Lemma interp_prems_elements u :
      interp_prems u = fold_right join (interp_expr (to_nonempty_list u).1) (List.map (interp_expr) (to_nonempty_list u).2).
    Proof.
      rewrite /interp_prems.
      have he := to_nonempty_list_spec u.
      destruct to_nonempty_list.
      now rewrite fold_right_map.
    Qed.

    Lemma fold_right_interp {x l x' l'} :
      equivlistA Logic.eq (x :: l) (x' :: l') ->
      fold_right join (interp_expr x) (List.map (interp_expr) l) ≡ fold_right join (interp_expr x') (List.map (interp_expr) l').
    Proof.
      intros eq. apply fold_right_equivlist_all.
      intros a. rewrite !InA_In_eq.
      rewrite !(in_map_iff (interp_expr) (_ :: _)).
      setoid_rewrite <-InA_In_eq.
      split.
      - move=> [b [<- ]].
        eexists; split; trea. now apply eq in b0.
      - move=> [b [<- ]].
        eexists; split; trea. now apply eq in b0.
    Qed.

    Lemma equivlistA_add le u : let l := to_nonempty_list (NonEmptyLevelExprSet.add le u) in
      equivlistA Logic.eq (l.1 :: l.2) (le :: LevelExprSet.elements u).
    Proof.
      have he := to_nonempty_list_spec (NonEmptyLevelExprSet.add le u).
      destruct to_nonempty_list. cbn.
      intros x. rewrite he.
      rewrite !LevelExprSet.elements_spec1.
      split.
      - move/LevelExprSet.add_spec => [->|hin].
        now constructor. constructor 2. now apply LevelExprSet.elements_spec1.
      - intros h; depelim h; subst. now apply LevelExprSet.add_spec; left.
        apply LevelExprSet.add_spec. now apply LevelExprSet.elements_spec1 in h.
    Qed.

    Lemma interp_prems_add le (u : t) :
      interp_prems (NonEmptyLevelExprSet.add le u) ≡ join (interp_expr le) (interp_prems u).
    Proof.
      rewrite 2!interp_prems_elements.
      erewrite fold_right_interp. 2:apply equivlistA_add.
      rewrite fold_right_comm.
      { apply map_nil, elements_not_empty. }
      apply join_congr_r. eapply fold_right_equivlist_all.
      have he := to_nonempty_list_spec u.
      destruct to_nonempty_list. rewrite -he //=.
    Qed.

    Lemma interp_prems_elim (P : t -> S -> Prop) :
      Proper (Logic.eq ==> eq ==> iff) P ->
      (forall le, P (singleton le) (interp_expr le)) ->
      (forall le u k, P u k -> ~ LevelExprSet.In le u -> P (NonEmptyLevelExprSet.add le u) (join (interp_expr le) k)) ->
      forall u, P u (interp_prems u).
    Proof.
      intros prop hs hadd.
      eapply elim.
      - intros le. rewrite interp_prems_singleton. apply hs.
      - intros le prems ih hnin.
        rewrite interp_prems_add. now apply hadd.
    Qed.

    Lemma interp_add_prems n e : interp_prems (add_prems n e) ≡ add n (interp_prems e).
    Proof.
      revert e.
      refine (interp_prems_elim (fun u z => interp_prems (add_prems n u) ≡ add n z) _ _ _).
      - intros p p' eq a a' eq'.
        subst p'. now rewrite eq'.
      - intros le.
        rewrite add_prems_singleton interp_prems_singleton //=.
        destruct le; cbn. now rewrite add_distr.
      - intros le u k heq hnin.
        rewrite add_prems_add.
        rewrite interp_prems_add heq interp_add_expr.
        now rewrite add_join.
    Qed.

    Lemma interp_prems_in {le} {u : t} :
      LevelExprSet.In le u -> interp_expr le ≤ interp_prems u.
    Proof.
      revert u.
      refine (interp_prems_elim (fun u z => LevelExprSet.In le u -> interp_expr le ≤ z) _ _ _).
      - intros ? ? <- x y eq. now rewrite eq.
      - intros le' u'.
        apply LevelExprSet.singleton_spec in u'. red in u'; subst.
        reflexivity.
      - move=> le' u z hz hnin /LevelExprSet.add_spec [->|hin].
        * apply join_le_left.
        * specialize (hz hin).
          now apply join_le_right_trans.
    Qed.

    Lemma interp_prems_union {x y : t} :
      interp_prems (x ∪ y) ≡
      join (interp_prems x) (interp_prems y).
    Proof.
      move: x; apply elim.
      - intros []. rewrite union_comm union_add_singleton.
        now rewrite interp_prems_add interp_prems_singleton.
      - intros le' x ih hnin.
        rewrite union_add_distr !interp_prems_add ih. cbn.
        now rewrite join_assoc.
    Qed.

    Lemma interp_prems_subset {u u' : t} : u ⊂_leset u' ->
      interp_prems u ≤ interp_prems u'.
    Proof.
      intros hsub.
      revert u u' hsub.
      refine (interp_prems_elim (fun u z => forall u' : t, u ⊂_leset u' ->
        z ≤ interp_prems u') _ _ _).
      - intros ?? <- ?? eq.
        now setoid_rewrite eq.
      - intros le u' hsing.
        specialize (hsing le). forward hsing by now apply LevelExprSet.singleton_spec.
        now apply interp_prems_in.
      - intros le u k ih hin u' sub.
        have hle := sub le.
        specialize (ih u').
        forward ih. intros x hin'. apply sub. now apply LevelExprSet.add_spec; right.
        forward hle by now apply LevelExprSet.add_spec; left.
        have hi := interp_prems_in hle.
        apply join_le_left_eq. split => //.
    Qed.

  End SemilatticeInterp.

End NonEmptyLevelExprSet.
