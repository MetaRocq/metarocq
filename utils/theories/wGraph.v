From Stdlib Require Import ZArith Zcompare Lia ssrbool.
From Stdlib Require Import MSetAVL MSetFacts MSetProperties.
From MetaRocq.Utils Require Import MRUtils.
From Stdlib Require Import ssreflect.
From Equations Require Import Equations.

Local Open Scope Z_scope.

Ltac Tauto.intuition_solver ::= auto with core arith zarith bool datatypes crelations relations.

Lemma fold_max_In n m l (H : fold_left Z.max l n = m)
  : n = m \/ In m l.
Proof.
  revert n H; induction l; cbn; intros n H.
  intuition.
  apply IHl in H.
  apply or_assoc. destruct H; [left|now right]. lia.
Qed.

Lemma fold_max_le n m l (H : n <= m \/ Exists (Z.le n) l)
  : n <= fold_left Z.max l m.
Proof.
  revert m H; induction l; cbn in *; intros m [H|H].
  assumption. inversion H.
  eapply IHl. left; lia.
  eapply IHl. inversion_clear H.
  left; lia. right; assumption.
Qed.

Lemma fold_max_le' n m l (H : In n (m :: l))
  : n <= fold_left Z.max l m.
Proof.
  apply fold_max_le. destruct H.
  left; lia. right. apply Exists_exists.
  eexists. split. eassumption. reflexivity.
Qed.

Definition eq_max n m k : max n m = k -> n = k \/ m = k.
  intro; lia.
Qed.

Module Nbar.
  (* None is -∞ *)
  Definition t := option Z.
  Definition max (n m : t) : t :=
    match n, m with
    | Some n, Some m => Some (Z.max n m)
    | Some n, None => Some n
    | None, Some m => Some m
    | _, _ => None
    end.
  Definition add (n m : t) : t :=
    match n, m with
    | Some n, Some m => Some (n + m)
    | _, _ => None
    end.

  Definition sub (n m : t) : t :=
    match n, m with
    | Some n, Some m => Some (n - m)
    | _, _ => None
    end.

  Definition S : t -> t := option_map Z.succ.

  Definition le (n m : t) : Prop :=
    match n, m with
    | Some n, Some m => n <= m
    | Some _, None => False
    | None, _ => True
    end.

  Definition lt (n m : t) : Prop :=
    match n, m with
    | Some n, Some m => n < m
    | None, Some _ => True
    | _, None => False
    end.

  Arguments max _ _ : simpl nomatch.
  Arguments sub _ _ : simpl nomatch.
  Arguments add _ _ : simpl nomatch.
  Arguments le _ _ : simpl nomatch.
  Arguments lt _ _ : simpl nomatch.

  Declare Scope nbar_scope.
  Infix "+" := add : nbar_scope.
  Infix "-" := sub : nbar_scope.
  Infix "<=" := le : nbar_scope.
  Infix "<" := lt : nbar_scope.
  Delimit Scope nbar_scope with nbar.
  Bind Scope nbar_scope with t.

  Local Open Scope nbar_scope.

  #[global] Instance le_refl : Reflexive le.
  Proof.
    intro x; destruct x; cbn; reflexivity.
  Defined.

  #[global] Instance le_trans : Transitive le.
  Proof.
    intros [x|] [y|] [z|]; cbn; intuition.
  Defined.

  (* Definition is_finite (n : t) := is_Some n. *)
  (* Definition is_finite_max (n m : t) *)
  (*   : is_finite (max n m) <-> is_finite n \/ is_finite m. *)
  (* Proof. *)
  (*   split. *)
  (*   - destruct n, m; cbn; intros [k e]; try discriminate. *)
  (*     apply some_inj, eq_max in e. *)
  (*     destruct e; [left|right]; eexists; f_equal; eassumption. *)
  (*     left; eexists; reflexivity. *)
  (*     right; eexists; reflexivity. *)
  (*   - intros [H|H]. *)
  (*     destruct H as [n' e]; rewrite e; cbn. *)
  (*     destruct m; eexists; reflexivity. *)
  (*     destruct H as [m' e]; rewrite e; cbn. *)
  (*     destruct n; eexists; reflexivity. *)
  (* Defined. *)
  (* Definition is_finite_add (n m : t) *)
  (*   : is_finite (n + m) <-> is_finite n /\ is_finite m. *)
  (* Proof. *)
  (*   split. *)
  (*   - destruct n, m; cbn; intros [k e]; try discriminate. *)
  (*     split; eexists; reflexivity. *)
  (*   - intros [[n1 e1] [n2 e2]]; rewrite e1, e2. *)
  (*     eexists; reflexivity. *)
  (* Defined. *)

  (* Definition is_pos (n : t) := Some 1 <= n. *)
  (* Definition is_pos_max (n m : t) *)
  (*   : is_pos (max n m) -> is_pos n \/ is_pos m. *)
  (* Proof. *)
  (*   destruct n, m; cbn; intuition. lia. *)
  (* Defined. *)
  (* Definition is_pos_add (n m : t) *)
  (*   : is_pos (n + m) -> is_pos n \/ is_pos m. *)
  (* Proof. *)
  (*   destruct n, m; cbn; intuition. lia. *)
  (* Defined. *)

  (* Definition is_pos_is_finite n : is_pos n -> is_finite n. *)
  (* Proof. *)
  (*   destruct n; cbn; [|intuition]. *)
  (*   destruct n. lia. intros _. eexists; reflexivity. *)
  (* Qed. *)
  Lemma add_finite z1 z2 : Some (z1 + z2)%Z = Some z1 + Some z2.
  Proof. reflexivity. Qed.

  Definition add_assoc n m p : n + (m + p) = n + m + p.
  Proof.
    destruct n, m, p; try reflexivity; cbn.
    now rewrite Z.add_assoc.
  Defined.

  Definition add_0_r n : (n + Some 0 = n)%nbar.
  Proof.
    destruct n; try reflexivity; cbn.
    now rewrite Z.add_0_r.
  Defined.

  Lemma add_0_l n : (Some 0 + n = n)%nbar.
  Proof. by case: n. Qed.

  Lemma sub_diag n : n - n = match n with None => None | Some _ => Some 0 end.
  Proof. destruct n; simpl. now rewrite Z.sub_diag. auto. Defined.

  Lemma max_None n : max n None = n.
  Proof. destruct n; simpl; auto. Qed.

  Definition max_lub n m p : n <= p -> m <= p -> max n m <= p.
  Proof.
    destruct n, m, p; cbn; intuition lia.
  Defined.

  Definition add_max_distr_r n m p : max (n + p) (m + p) = max n m + p.
  Proof.
    destruct n, m, p; try reflexivity; cbn.
    now rewrite Z.add_max_distr_r.
  Defined.

  Definition max_le' n m p : p <= n \/ p <= m -> p <= max n m.
  Proof.
    destruct n, m, p; cbn; intuition; lia.
  Defined.

  Definition plus_le_compat_l n m p : n <= m -> p + n <= p + m.
  Proof.
    destruct n, m, p; cbn; intuition.
  Defined.

  Definition plus_le_compat n m p q : n <= m -> p <= q -> n + p <= m + q.
  Proof.
    destruct n, m, p, q; cbn; intuition.
  Defined.

  Definition max_idempotent n : max n n = n.
  Proof.
    destruct n; try reflexivity; cbn.
    now rewrite Z.max_idempotent.
  Defined.

  Lemma eq_max n m k (H : max n m = k) : n = k \/ m = k.
  Proof.
    destruct n, m; simpl in *.
    destruct (Z.max_spec z z0); intuition congruence.
    all:intuition.
  Qed.

  Lemma fold_max_In n m l (H : fold_left max l n = m)
    : n = m \/ In m l.
  Proof.
    revert n H; induction l; cbn; intros n H.
    intuition.
    apply IHl in H.
    apply or_assoc. destruct H; [left|now right].
    now apply eq_max.
  Qed.

  Lemma fold_max_le n m l (H : n <= m \/ Exists (le n) l)
    : n <= fold_left max l m.
  Proof.
    revert m H; induction l; cbn in *; intros m [H|H].
    assumption. inversion H.
    eapply IHl. left. apply max_le'; now left.
    eapply IHl. inversion_clear H.
    left. apply max_le'; now right.
    right; assumption.
  Qed.

  Lemma fold_max_le' n m l (H : In n (m :: l))
    : n <= fold_left max l m.
  Proof.
    apply fold_max_le. destruct H.
    left; subst; reflexivity.
    right. apply Exists_exists.
    eexists. split. eassumption. reflexivity.
  Qed.

  Lemma le_dec n m : {n <= m} + {~ n <= m}.
  Proof.
    destruct n as [n|], m as [m|]; cbn.
    simpl. destruct (n ?= m) eqn:comp. left.
    destruct (Z.compare_spec n m); subst; auto; try lia. discriminate.
    eapply (proj1 (Z.compare_lt_iff _ _)) in comp. left; lia.
    eapply (proj1 (Z.compare_gt_iff _ _)) in comp. right; lia.
    all: intuition.
  Defined.

  Lemma le_lt_dec n m : ({n <= m} + {m < n})%nbar.
  Proof.
    destruct n as [n|], m as [m|]; cbn.
    simpl. destruct (n ?= m) eqn:comp. left.
    destruct (Z.compare_spec n m); subst; auto; try lia. discriminate.
    eapply (proj1 (Z.compare_lt_iff _ _)) in comp. left; lia.
    eapply (proj1 (Z.compare_gt_iff _ _)) in comp. right; lia.

    all: (right; constructor) || (left; constructor).
  Defined.

  Lemma le_plus_r n m : (0 <= n)%Z -> m <= Some n + m.
  Proof.
    destruct m; cbn; lia.
  Qed.

  Lemma le_antisymm {n m} : n <= m -> m <= n -> n = m.
  Proof.
    destruct n, m; cbn; try easy.
  Qed.

End Nbar.

Import Nbar.

From Stdlib Require Import MSetDecide MSetInterface.

Module WeightedGraph (V : UsualOrderedType) (VSet : MSetInterface.S with Module E := V).
  Module VSetFact := WFactsOn V VSet.
  Module VSetProp := WPropertiesOn V VSet.
  Module VSetDecide := WDecide (VSet).
  Ltac sets := VSetDecide.fsetdec.

  (** Lemmas on sets *)

  Lemma VSet_add_remove x y p :
    x <> y ->
    VSet.Equal (VSet.add x (VSet.remove y p)) (VSet.remove y (VSet.add x p)).
  Proof. now sets. Qed.

  Lemma VSet_remove_add x p :
    ~ VSet.In x p ->
    VSet.Equal (VSet.remove x (VSet.add x p)) p.
  Proof. now sets. Qed.


  Lemma VSet_add_add x y p :
    VSet.Equal (VSet.add x (VSet.add y p)) (VSet.add y (VSet.add x p)).
  Proof. now sets. Qed.

  Lemma VSet_add_add_same x p :
    VSet.Equal (VSet.add x (VSet.add x p)) (VSet.add x p).
  Proof. now sets. Qed.

  Definition Disjoint s s' :=
    VSet.Empty (VSet.inter s s').

  Definition DisjointAdd x s s' := VSetProp.Add x s s' /\ ~ VSet.In x s.

  Lemma DisjointAdd_add1 {s0 s1 s2 x y}
        (H1 : DisjointAdd x s0 s1) (H2 : DisjointAdd y s1 s2)
    : DisjointAdd x (VSet.add y s0) s2.
  Proof.
    split.
    intro z; split; intro Hz. 2: destruct Hz as [Hz|Hz].
    - apply H2 in Hz. destruct Hz as [Hz|Hz]; [right|].
      now apply VSetFact.add_1.
      apply H1 in Hz. destruct Hz as [Hz|Hz]; [left; assumption|right].
      now apply VSetFact.add_2.
    - apply H2. right; apply H1. now left.
    - apply H2. apply VSet.add_spec in Hz.
      destruct Hz as [Hz|Hz]; [now left|right].
      apply H1. now right.
    - intro Hx. apply VSet.add_spec in Hx.
      destruct Hx as [Hx|Hx].
      subst. apply H2. apply H1. now left.
      now apply H1.
  Qed.

  Lemma DisjointAdd_add2 {s x} (H : ~ VSet.In x s)
    : DisjointAdd x s (VSet.add x s).
  Proof.
    split. apply VSetProp.Add_add.
    assumption.
  Qed.

  Lemma DisjointAdd_add3  {s0 s1 s2 x y}
        (H1 : DisjointAdd x s0 s1) (H2 : DisjointAdd y s1 s2)
    : DisjointAdd y s0 (VSet.add y s0).
  Proof.
    apply DisjointAdd_add2. intro H.
    unfold DisjointAdd in *.
    apply H2. apply H1. now right.
  Qed.



  Lemma DisjointAdd_remove {s s' x y} (H : DisjointAdd x s s') (H' : x <> y)
    : DisjointAdd x (VSet.remove y s) (VSet.remove y s').
  Proof.
    repeat split. 2: intros [H0|H0].
    - intro H0. apply VSet.remove_spec in H0.
      destruct H0 as [H0 H1].
      pose proof ((H.p1 y0).p1 H0) as H2.
      destruct H2; [now left|right].
      apply VSetFact.remove_2; intuition.
    - subst. apply VSet.remove_spec. split; [|assumption].
      apply H.p1. left; reflexivity.
    - apply VSet.remove_spec in H0; destruct H0 as [H0 H1].
      apply VSet.remove_spec; split; [|assumption].
      apply H.p1. right; assumption.
    - intro H0. apply VSet.remove_spec in H0; destruct H0 as [H0 _].
      apply H; assumption.
  Qed.

  Lemma DisjointAdd_Subset {x s s'}
    : DisjointAdd x s s' -> VSet.Subset s s'.
  Proof.
    intros [H _] z Hz. apply H; intuition.
  Qed.

  Lemma DisjointAdd_union {s s' s'' x} (H : DisjointAdd x s s')
    : ~ VSet.In x s'' -> DisjointAdd x (VSet.union s s'') (VSet.union s' s'').
  Proof.
    destruct H as [hadd hin].
    split.
    now eapply VSetProp.union_Add. sets.
  Qed.

  Lemma DisjointAdd_remove1 {s x} (H : VSet.In x s)
    : DisjointAdd x (VSet.remove x s) s.
  Proof.
    split.
    - intro z; split; intro Hz. 2: destruct Hz as [Hz|Hz].
      + destruct (V.eq_dec x z). now left.
        right. now apply VSetFact.remove_2.
      + now subst.
      + eapply VSetFact.remove_3; eassumption.
    - now apply VSetFact.remove_1.
  Qed.


  Global Instance Add_Proper : Proper (eq ==> VSet.Equal ==> VSet.Equal ==> iff) VSetProp.Add.
  Proof.
    intros x y -> s0 s1 eq s0' s1' eq'.
    unfold VSetProp.Add. now setoid_rewrite eq; setoid_rewrite eq'.
  Qed.

  Global Instance DisjointAdd_Proper : Proper (eq ==> VSet.Equal ==> VSet.Equal ==> iff) DisjointAdd.
  Proof.
    intros x y -> s0 s1 eq s0' s1' eq'.
    unfold DisjointAdd.
    now rewrite eq eq'.
  Qed.

  Lemma Add_In {s x} (H : VSet.In x s)
    : VSetProp.Add x s s.
  Proof.
    split. intuition.
    intros []; try subst; assumption.
  Qed.

  Lemma Add_Add {s s' x} (H : VSetProp.Add x s s')
    : VSetProp.Add x s' s'.
  Proof.
    apply Add_In, H. left; reflexivity.
  Qed.

  Lemma Disjoint_DisjointAdd x s s' s'' :
    DisjointAdd x s s' ->
    Disjoint s' s'' ->
    Disjoint s s''.
  Proof.
    intros da; unfold Disjoint.
    intros disj i. specialize (disj i).
    intros ininter; apply disj.
    eapply DisjointAdd_Subset in da.
    sets.
  Qed.

  Lemma DisjointAdd_remove_add {x s} :
    DisjointAdd x (VSet.remove x s) (VSet.add x s).
  Proof. split; [intro|]; sets. Qed.

  Lemma DisjointAdd_Equal x s s' s'' : DisjointAdd x s s' -> VSet.Equal s' s'' -> DisjointAdd x s s''.
  Proof. now intros d <-. Qed.

  Lemma DisjointAdd_Equal_l x s s' s'' : DisjointAdd x s s' -> VSet.Equal s s'' -> DisjointAdd x s'' s'.
  Proof. now intros d <-. Qed.

  Lemma DisjointAdd_remove_inv {x s s' z} : DisjointAdd x s (VSet.remove z s') ->
    VSet.Equal s (VSet.remove z s).
  Proof.
    intros [].
    intros i. rewrite VSet.remove_spec.
    intuition auto. red in H2; subst.
    specialize (proj2 (H z) (or_intror H1)).
    rewrite VSet.remove_spec.
    intuition.
  Qed.

  Module Edge.
    Definition t := (V.t * Z * V.t)%type.
    Definition eq : t -> t -> Prop := eq.
    Definition eq_equiv : RelationClasses.Equivalence eq := _.

    Definition lt : t -> t -> Prop :=
      fun '(x, n, y) '(x', n', y') => (V.lt x x') \/ (V.eq x x' /\ n < n')
                                   \/ (V.eq x x' /\ n = n' /\ V.lt y y').
    Definition lt_strorder : StrictOrder lt.
      split.
      - intros [[x n] y] H; cbn in H. intuition.
        all: eapply V.lt_strorder; eassumption.
      - intros [[x1 n1] y1] [[x2 n2] y2] [[x3 n3] y3] H1 H2; cbn in *.
        pose proof (StrictOrder_Transitive x1 x2 x3) as T1.
        pose proof (StrictOrder_Transitive y1 y2 y3) as T2.
        pose proof (@eq_trans _ n1 n2 n3) as T3.
        unfold VSet.E.lt in *. unfold V.eq in *.
        destruct H1 as [H1|[[H1 H1']|[H1 [H1' H1'']]]];
          destruct H2 as [H2|[[H2 H2']|[H2 [H2' H2'']]]]; subst; intuition.
    Qed.
    Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
      intros x x' H1 y y' H2. now subst.
    Qed.
    Definition compare : t -> t -> comparison
      := fun '(x, n, y) '(x', n', y') => match V.compare x x' with
                                      | Lt => Lt
                                      | Gt => Gt
                                      | Eq => match Z.compare n n' with
                                             | Lt => Lt
                                             | Gt => Gt
                                             | Eq => V.compare y y'
                                             end
                                      end.
    Definition compare_spec :
      forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
      intros [[x1 n1] y1] [[x2 n2] y2]; cbn.
      pose proof (V.compare_spec x1 x2) as H1.
      destruct (V.compare x1 x2); cbn in *; inversion_clear H1.
      2-3: constructor; intuition.
      subst. pose proof (Z.compare_spec n1 n2) as H2.
      destruct (n1 ?= n2); cbn in *; inversion_clear H2.
      2-3: constructor; intuition.
      subst. pose proof (V.compare_spec y1 y2) as H3.
      destruct (V.compare y1 y2); cbn in *; inversion_clear H3;
        constructor; subst; intuition.
    Defined.

    Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
      unfold eq. decide equality. apply V.eq_dec.
      decide equality. apply Z.eq_dec. apply V.eq_dec.
    Defined.
    Definition eqb : t -> t -> bool := fun x y => match compare x y with
                                          | Eq => true
                                          | _ => false
                                          end.

    Definition eq_leibniz : forall x y, eq x y -> x = y := fun x y eq => eq.

  End Edge.
  Module EdgeSet:= MSetAVL.Make Edge.
  Module EdgeSetFact := WFactsOn Edge EdgeSet.
  Module EdgeSetProp := WPropertiesOn Edge EdgeSet.
  Module EdgeSetDecide := WDecide (EdgeSet).
  Ltac esets := EdgeSetDecide.fsetdec.

  Definition t := (VSet.t * EdgeSet.t * V.t)%type.

  Local Definition V (G : t) := fst (fst G).
  Local Definition E (G : t) := snd (fst G).
  Local Definition s (G : t) := snd G.

  Definition e_source : Edge.t -> V.t := fst ∘ fst.
  Definition e_target : Edge.t -> V.t := snd.
  Definition e_weight : Edge.t -> Z := snd ∘ fst.
  Notation "x ..s" := (e_source x) (at level 3, format "x '..s'").
  Notation "x ..t" := (e_target x) (at level 3, format "x '..t'").
  Notation "x ..w" := (e_weight x) (at level 3, format "x '..w'").

  Definition opp_edge (e : Edge.t) : Edge.t :=
    (e..t, - e..w, e..s).

  Definition labelling := V.t -> nat.

  Section graph.
    Context (G : t).

    Definition add_node x : t :=
      (VSet.add x (V G), (E G), (s G)).

    Definition add_edge e : t :=
      (VSet.add e..s (VSet.add e..t (V G)),
      EdgeSet.add e (E G), (s G)).

    Definition EdgeOf x y := ∑ n, EdgeSet.In (x, n, y) (E G).

    Inductive PathOf : V.t -> V.t -> Type :=
    | pathOf_refl x : PathOf x x
    | pathOf_step x y z : EdgeOf x y -> PathOf y z -> PathOf x z.

    Arguments pathOf_step {x y z} e p.

    Fixpoint weight {x y} (p : PathOf x y) :=
      match p with
      | pathOf_refl x => 0
      | pathOf_step e p => e.π1 + weight p
      end.

    Fixpoint nodes {x y} (p : PathOf x y) : VSet.t :=
      match p with
      | pathOf_refl x => VSet.empty
      | pathOf_step e p => VSet.add x (nodes p)
      end.

    Fixpoint concat {x y z} (p : PathOf x y) : PathOf y z -> PathOf x z :=
      match p with
      | pathOf_refl _ => fun q => q
      | pathOf_step e p => fun q => pathOf_step e (concat p q)
      end.

    Fixpoint length {x y} (p : PathOf x y) :=
      match p with
      | pathOf_refl x => 0
      | pathOf_step e p => Z.succ (length p)
      end.

    Class invariants := mk_invariant
      { edges_vertices : (* E ⊆ V × V *)
         (forall e, EdgeSet.In e (E G) -> VSet.In e..s (V G) /\ VSet.In e..t (V G));
        (* s ∈ V *)
        source_vertex : VSet.In (s G) (V G);
        (* s is a source that is lower than any other node *)
        source_pathOf : forall x, VSet.In x (V G) -> ∥ ∑ p : PathOf (s G) x, ∥ 0 <= weight p ∥ ∥ }.

    Definition PosPathOf x y := exists p : PathOf x y, weight p > 0.

    Class acyclic_no_loop
      := Build_acyclic_no_loop : forall x (p : PathOf x x), weight p <= 0.

    Definition acyclic_no_loop' := forall x, ~ (PosPathOf x x).

    Fact acyclic_no_loop_loop' : acyclic_no_loop <-> acyclic_no_loop'.
    Proof using Type.
      unfold acyclic_no_loop, acyclic_no_loop', PosPathOf.
      split.
      - intros H x [p HH]. specialize (H x p). lia.
      - intros H x p. firstorder.
    Qed.

    Definition correct_labelling (l : labelling) :=
      l (s G) = 0%nat /\
      forall e, EdgeSet.In e (E G) -> Z.of_nat (l e..s) + e..w <= Z.of_nat (l e..t).

    Definition leq_vertices n x y := forall l, correct_labelling l -> Z.of_nat (l x) + n <= Z.of_nat (l y).

    Inductive SPath : VSet.t -> V.t -> V.t -> Type :=
    | spath_refl s x : SPath s x x
    | spath_step s s' x y z : DisjointAdd x s s' -> EdgeOf x y
                               -> SPath s y z -> SPath s' x z.

    Arguments spath_step {s s' x y z} H e p.
    Derive Signature NoConfusion for SPath.

    (* Global Instance SPath_refl s : CRelationClasses.Reflexive (SPath s) *)
    (*   := spath_refl s. *)

    Fixpoint to_pathOf {s x y} (p : SPath s x y) : PathOf x y :=
      match p with
      | spath_refl _ x => pathOf_refl x
      | spath_step _ e p => pathOf_step e (to_pathOf p)
      end.

    Fixpoint sweight {s x y} (p : SPath s x y) :=
      match p with
      | spath_refl _ _ => 0
      | spath_step _ e p => e.π1 + sweight p
      end.

    Lemma sweight_weight {s x y} (p : SPath s x y)
      : sweight p = weight (to_pathOf p).
    Proof using Type.
      induction p; cbn; lia.
    Qed.

    Fixpoint is_simple {x y} (p : PathOf x y) :=
      match p with
      | pathOf_refl x => true
      | @pathOf_step x y z e p => negb (VSet.mem x (nodes p)) && is_simple p
      end.

    Program Definition to_simple : forall {x y} (p : PathOf x y),
        is_simple p = true -> SPath (nodes p) x y
      := fix to_simple {x y} p (Hp : is_simple p = true) {struct p} :=
           match
             p in PathOf t t0
             return is_simple p = true -> SPath (nodes p) t t0
           with
           | pathOf_refl x =>
             fun _ => spath_refl (nodes (pathOf_refl x)) x
           | @pathOf_step x y z e p0 =>
             fun Hp0 => spath_step _ e (to_simple p0 _)
           end Hp.
    Next Obligation.
      split.
      - eapply VSetProp.Add_add.
      - apply andb_andI in Hp0 as [h1 h2].
        apply negb_true_iff in h1. apply VSetFact.not_mem_iff in h1.
        assumption.
    Defined.

    Lemma weight_concat {x y z} (p : PathOf x y) (q : PathOf y z)
      : weight (concat p q) = weight p + weight q.
    Proof using Type.
      revert q; induction p; intro q; cbn.
      reflexivity. specialize (IHp q); intuition.
    Qed.

    Fixpoint add_end {s x y} (p : SPath s x y)
      : forall {z} (e : EdgeOf y z) {s'} (Hs : DisjointAdd y s s'), SPath s' x z
      := match p with
         | spath_refl s x => fun z e s' Hs => spath_step Hs e (spath_refl _ _)
         | spath_step H e p
           => fun z e' s' Hs => spath_step (DisjointAdd_add1 H Hs) e
                                        (add_end p e' (DisjointAdd_add3 H Hs))
         end.

    Lemma weight_add_end {s x y} (p : SPath s x y) {z e s'} Hs
      : sweight (@add_end s x y p z e s' Hs) = sweight p + e.π1.
    Proof using Type.
      revert z e s' Hs. induction p.
      - intros; cbn; lia.
      - intros; cbn. rewrite IHp; lia.
    Qed.


   (* Fixpoint split {s x y} (p : SPath s x y) *)
   (*   : SPath (VSet.remove y s) x y * ∑ s', SPath s' y y := *)
   (*    match p with *)
   (*    | spath_refl s x => (spath_refl _ x, (VSet.empty; spath_refl _ x)) *)
   (*    | spath_step s s' x0 y0 z0 H e p0 *)
   (*      => match V.eq_dec x0 z0 with *)
   (*        | left pp => (eq_rect _ (SPath _ _) (spath_refl _ _) _ pp, *)
   (*                     (s'; eq_rect _ (fun x => SPath _ x _) *)
   (*                                  (spath_step H e p0) _ pp)) *)
   (*        | right pp => (spath_step (DisjointAdd_remove H pp) e (split p0).1, *)
   (*                      (split p0).2) *)
   (*        end *)
   (*    end. *)

    Definition SPath_sub {s s' x y}
      : VSet.Subset s s' -> SPath s x y -> SPath s' x y.
    Proof.
      intros Hs p; revert s' Hs; induction p.
      - constructor.
      - intros s'0 Hs. unshelve econstructor.
        exact (VSet.remove x s'0).
        3: eassumption. 2: eapply IHp.
        + split. apply VSetProp.Add_remove.
          apply Hs, d; intuition.
          now apply VSetProp.FM.remove_1.
        + intros u Hu. apply VSetFact.remove_2.
          intro X. apply d. subst; assumption.
          apply Hs, d; intuition.
    Defined.

    Definition weight_SPath_sub {s s' x y} Hs p
      : sweight (@SPath_sub s s' x y Hs p) = sweight p.
    Proof using Type.
      revert s' Hs; induction p; simpl. reflexivity.
      intros s'0 Hs. now rewrite IHp.
    Qed.

    Obligation Tactic := Program.Tactics.program_simpl.
    Program Fixpoint sconcat {s s' x y z} (p : SPath s x y) : Disjoint s s' ->
      SPath s' y z -> SPath (VSet.union s s') x z :=
      match p in SPath s x y return Disjoint s s' -> SPath s' y z -> SPath (VSet.union s s') x z  with
      | spath_refl _ _ => fun hin q => SPath_sub _ q
      | @spath_step s s0 x y z' da e p => fun hin q =>
        @spath_step (VSet.union s s') _ x y z _ e (@sconcat _ _ _ _ _ p _ q)
      end.
    Next Obligation. sets. Qed.
    Next Obligation.
      eapply DisjointAdd_union; eauto.
      destruct da. unfold Disjoint in hin.
      intros inxs'. apply (hin x).
      destruct (H x). specialize (H2 (or_introl eq_refl)).
      now eapply VSet.inter_spec.
    Qed.
    Next Obligation.
      eapply Disjoint_DisjointAdd in hin; eauto.
    Qed.

    Lemma sweight_sconcat {s s' x y z} (p : SPath s x y) (ss' : Disjoint s s')
          (q : SPath s' y z) :
      sweight (sconcat p ss' q) = sweight p + sweight q.
    Proof using Type.
     induction p; cbn.
     1: by apply: weight_SPath_sub.
     rewrite IHp; lia.
    Qed.

    Fixpoint snodes {s x y} (p : SPath s x y) : VSet.t :=
      match p with
      | spath_refl s x => VSet.empty
      | spath_step H e p => VSet.add x (snodes p)
      end.


    Definition split {s x y} (p : SPath s x y)
      : forall u, {VSet.In u (snodes p)} + {u = y} ->
        SPath (VSet.remove u s) x u * SPath s u y.
    Proof.
      induction p; intros u Hu; cbn in *.
      - induction Hu. eapply False_rect, VSet.empty_spec; eassumption.
        subst. split; constructor.
      - induction (V.eq_dec x u) as [Hx|Hx].
        + split. subst; constructor.
          econstructor; try eassumption; subst; eassumption.
        + assert (Hu' : {VSet.In u (snodes p)} + {u = z}). {
            induction Hu as [Hu|Hu].
            apply (VSetFact.add_3 Hx) in Hu. now left.
            now right. }
          specialize (IHp _ Hu'). split.
          * econstructor. 2: eassumption. 2: exact IHp.1.
            now apply DisjointAdd_remove.
          * eapply SPath_sub. 2: exact IHp.2.
            eapply DisjointAdd_Subset; eassumption.
    Defined.

    Lemma weight_split {s x y} (p : SPath s x y) {u Hu}
      : sweight (split p u Hu).1 + sweight (split p u Hu).2 = sweight p.
    Proof using Type.
      induction p.
      - destruct Hu as [Hu|Hu]. simpl in Hu.
        now exfalso; eapply VSetFact.empty_iff in Hu.
        destruct Hu; reflexivity.
      - simpl. destruct (V.eq_dec x u) as [X|X]; simpl.
        + destruct X; reflexivity.
        + rewrite weight_SPath_sub.
          rewrite <- Z.add_assoc.
          now rewrite IHp.
    Qed.

   (* Fixpoint split {s x y} (p : SPath s x y) *)
   (*   : SPath (VSet.remove y s) x y * SPath s y y := *)
   (*    match p with *)
   (*    | spath_refl s x => (spath_refl _ x, spath_refl _ x) *)
   (*    | spath_step s s' x0 y0 z0 H e p0 *)
   (*      => match V.eq_dec x0 z0 with *)
   (*        | left pp => (eq_rect _ (SPath _ _) (spath_refl _ _) _ pp, *)
   (*                     eq_rect _ (fun x => SPath _ x _) (spath_step H e p0) _ pp) *)
   (*        | right pp => (spath_step (DisjointAdd_remove H pp) e (split p0).1, *)
   (*                      SPath_sub (DisjointAdd_Subset H) (split p0).2) *)
   (*        end *)
   (*    end. *)

   (*  Lemma weight_split {s x y} (p : SPath s x y) *)
   (*    : sweight (split p).1 + sweight (split p).2 = sweight p. *)
   (*  Proof. *)
   (*    induction p. *)
   (*    - reflexivity. *)
   (*    - simpl. destruct (V.eq_dec x z). *)
   (*      + destruct e0; cbn. reflexivity. *)
   (*      + cbn. rewrite weight_SPath_sub; lia. *)
   (*  Qed. *)

    Definition split' {s x y} (p : SPath s x y)
      : SPath (VSet.remove y s) x y * SPath s y y
      := split p y (right eq_refl).

    Lemma weight_split' {s x y} (p : SPath s x y)
      : sweight (split' p).1 + sweight (split' p).2 = sweight p.
    Proof.
      unfold split'; apply weight_split.
    Defined.

    Definition spath_one {s x y k} (Hx : VSet.In x s) (Hk : EdgeSet.In (x, k, y) (E G))
      : SPath s x y.
    Proof.
      econstructor. 3: constructor. now apply DisjointAdd_remove1.
      exists k. assumption.
    Defined.

    Lemma simplify_aux1 {s0 s1 s2} (H : VSet.Equal (VSet.union s0 s1) s2)
      : VSet.Subset s0 s2.
    Proof using Type.
      intros x Hx. apply H.
      now apply VSetFact.union_2.
    Qed.

    Lemma simplify_aux2 {s0 x} (Hx : VSet.mem x s0 = true)
          {s1 s2}
          (Hs : VSet.Equal (VSet.union s0 (VSet.add x s1)) s2)
      : VSet.Equal (VSet.union s0 s1) s2.
    Proof using Type.
      apply VSet.mem_spec in Hx.
      etransitivity; [|eassumption].
      intro y; split; intro Hy; apply VSet.union_spec;
        apply VSet.union_spec in Hy; destruct Hy as [Hy|Hy].
      left; assumption.
      right; now apply VSetFact.add_2.
      left; assumption.
      apply VSet.add_spec in Hy; destruct Hy as [Hy|Hy].
      left; red in Hy; subst; assumption.
      right; assumption.
    Qed.

    Lemma simplify_aux3 {s0 s1 s2 x}
          (Hs : VSet.Equal (VSet.union s0 (VSet.add x s1)) s2)
      : VSet.Equal (VSet.union (VSet.add x s0) s1) s2.
    Proof using Type.
      etransitivity; [|eassumption].
      etransitivity. eapply VSetProp.union_add.
      symmetry. etransitivity. apply VSetProp.union_sym.
      etransitivity. eapply VSetProp.union_add.
      apply VSetFact.add_m. reflexivity.
      apply VSetProp.union_sym.
    Qed.

    Fixpoint simplify {s x y} (q : PathOf y x)
      : forall (p : SPath s x y) {s'},
        VSet.Equal (VSet.union s (nodes q)) s' -> ∑ x', SPath s' x' x' :=
      match q with
      | pathOf_refl x => fun p s' Hs => (x; SPath_sub (simplify_aux1 Hs) p)
      | @pathOf_step y y' _ e q =>
        fun p s' Hs => match VSet.mem y s as X return VSet.mem y s = X -> _ with
              | true => fun XX => let '(p1, p2) := split' p in
                       if 0 <? sweight p2
                       then (y; SPath_sub (simplify_aux1 Hs) p2)
                       else (simplify q (add_end p1 e
                                          (DisjointAdd_remove1 (VSetFact.mem_2 XX)))
                                      (simplify_aux2 XX Hs))
              | false => fun XX => (simplify q (add_end p e
                            (DisjointAdd_add2 ((VSetFact.not_mem_iff _ _).p2 XX)))
                                         (simplify_aux3 Hs))
              end eq_refl
      end.

    Lemma weight_simplify {s x y} q (p : SPath s x y)
      : forall {s'} Hs, (0 < weight q + sweight p)
        -> 0 < sweight (simplify q p (s':=s') Hs).π2.
    Proof using Type.
      revert s p; induction q.
      - cbn; intros. intuition. now rewrite weight_SPath_sub.
      - intros s p s' Hs H; cbn in H. simpl.
        set (F0 := proj2 (VSetFact.not_mem_iff s x)); clearbody F0.
        set (F1 := @VSetFact.mem_2 s x); clearbody F1.
        set (F2 := @simplify_aux2 s x); clearbody F2.
        destruct (VSet.mem x s).
        + case_eq (split' p); intros p1 p2 Hp.
          case_eq (0 <? sweight p2); intro eq.
          * cbn. apply Z.ltb_lt in eq.
            rewrite weight_SPath_sub; lia.
          * eapply IHq. rewrite weight_add_end.
            pose proof (weight_split' p) as X; rewrite Hp in X; cbn in X.
            apply Z.ltb_ge in eq. rewrite <- X in H. lia.
        + eapply IHq. rewrite weight_add_end. lia.
    Qed.

    Definition succs (x : V.t) : list (Z * V.t)
      := let l := List.filter (fun e => V.eq_dec e..s x) (EdgeSet.elements (E G)) in
         List.map (fun e => (e..w, e..t)) l.

    (* lsp = longest simple path *)
    (* l is the list of authorized intermediate nodes *)
    (* lsp0 (a::l) x y = max (lsp0 l x y) (lsp0 l x a + lsp0 l a y) *)

    Fixpoint lsp00 fuel (s : VSet.t) (x z : V.t) : Nbar.t :=
      let base := if V.eq_dec x z then Some 0 else None in
      match fuel with
      | 0%nat => base
      | Datatypes.S fuel =>
        match VSet.mem x s with
        | true =>
          let ds := List.map
                      (fun '(n, y) => Some n + lsp00 fuel (VSet.remove x s) y z)%nbar
                      (succs x) in
          List.fold_left Nbar.max ds base
        | false => base end
      end.

    Definition lsp0 s := lsp00 (VSet.cardinal s) s.

    Lemma lsp0_eq s x z : lsp0 s x z =
      let base := if V.eq_dec x z then Some 0 else None in
      match VSet.mem x s with
      | true =>
        let ds := List.map (fun '(n, y) => Some n + lsp0 (VSet.remove x s) y z)%nbar
                           (succs x) in
        List.fold_left Nbar.max ds base
      | false => base end.
    Proof using Type.
      unfold lsp0. set (fuel := VSet.cardinal s).
      cut (VSet.cardinal s = fuel); [|reflexivity].
      clearbody fuel. revert s x. induction fuel.
      - intros s x H.
        apply VSetProp.cardinal_inv_1 in H.
        specialize (H x). apply VSetProp.FM.not_mem_iff in H.
        rewrite H. reflexivity.
      - intros s x H. simpl.
        case_eq (VSet.mem x s); [|reflexivity].
        intro HH. f_equal. apply List.map_ext.
        intros [n y].
        assert (H': VSet.cardinal (VSet.remove x s) = fuel);
          [|rewrite H'; reflexivity].
        apply VSet.mem_spec, VSetProp.remove_cardinal_1 in HH.
        lia.
    Qed.

  (* lsp = longest simple path *)
  (* l is the list of authorized intermediate nodes *)
  (* lsp0 (a::l) x y = max (lsp0 l x y) (lsp0 l x a + lsp0 l a y) *)

  Fixpoint lsp00_fast fuel (s : VSet.t) (x z : V.t) : Nbar.t :=
    let base := if V.eq_dec x z then Some 0 else None in
    match fuel with
    | 0%nat => base
    | Datatypes.S fuel =>
      match VSet.mem x s with
      | true =>
        let s := VSet.remove x s in
        EdgeSet.fold
          (fun '(src, w, tgt) acc =>
            if V.eq_dec src x then
              Nbar.max acc (Some w + lsp00_fast fuel s tgt z)
            else acc)%nbar
           (E G) base
      | false => base end
    end.

  Lemma fold_left_map {A B C} (f : A -> B -> A) (g : C -> B) l acc : fold_left f (map g l) acc =
    fold_left (fun acc x => f acc (g x)) l acc.
  Proof using Type.
    induction l in acc |- *; cbn; auto.
  Qed.

  Lemma fold_left_filter {A B} (f : A -> B -> A) (g : B -> bool) l acc : fold_left f (filter g l) acc =
    fold_left (fun acc x => if g x then f acc x else acc) l acc.
  Proof using Type.
    induction l in acc |- *; cbn; auto.
    destruct (g a) => //=.
  Qed.

  #[global] Instance fold_left_proper {A B} : Proper (`≐2` ==> `≐2`) (@fold_left A B).
  Proof using Type.
    intros f g hfg x acc.
    induction x in acc |- * => //.
    cbn. rewrite (hfg acc a). apply IHx.
  Qed.

  Lemma fold_left_equiv {A B C} (f : A -> B -> A) (g : A -> C -> A) (h : C -> B) l l' acc :
    (forall acc x, f acc (h x) = g acc x) ->
    l = map h l' ->
    fold_left f l acc = fold_left g l' acc.
  Proof using Type.
    intros hfg ->.
    induction l' in acc |- *; cbn; auto.
    rewrite fold_left_map. rewrite hfg.
    apply fold_left_proper. exact hfg.
  Qed.

  Lemma lsp00_optim fuel s x z : lsp00_fast fuel s x z = lsp00 fuel s x z.
  Proof using Type.
    induction fuel in s, x, z |- *; auto. simpl.
    destruct VSet.mem => //.
    rewrite EdgeSet.fold_spec.
    rewrite fold_left_map.
    unfold succs. rewrite fold_left_map.
    rewrite fold_left_filter.
    eapply fold_left_proper => acc [[src w] tgt]; cbn.
    destruct is_left => //. f_equal. now rewrite IHfuel.
  Qed.

  Definition lsp_fast := lsp00_fast (VSet.cardinal (V G)) (V G).

    (* Equations lsp0 (s : VSet.t) (x z : V.t) : Nbar.t by wf (VSet.cardinal s) *)
    (*   := *)
    (*   lsp0 s x z := *)
    (*   let base := if V.eq_dec x z then Some 0 else None in *)
    (*   match VSet.mem x s as X return VSet.mem x s = X -> _ with *)
    (*   | true => fun XX => *)
    (*     let ds := List.map (fun '(n, y) => Some n + lsp0 (VSet.remove x s) y z)%nbar *)
    (*                        (succs x) in *)
    (*     List.fold_left Nbar.max ds base *)
    (*   | false => fun _ => base end eq_refl. *)
    (* Next Obligation. *)
    (*   apply VSet.mem_spec in XX. *)
    (*   pose proof (VSetProp.remove_cardinal_1 XX). *)
    (*   lia. *)
    (* Defined. *)

    Definition lsp := lsp0 (V G).

    Lemma lsp_optim x y : lsp_fast x y = lsp x y.
    Proof using Type.
      now rewrite /lsp /lsp_fast /lsp0 lsp00_optim.
    Qed.

    Lemma lsp0_VSet_Equal {s s' x y} :
      VSet.Equal s s' -> lsp0 s x y = lsp0 s' x y.
    Proof using Type.
      intro H; unfold lsp0; rewrite (VSetProp.Equal_cardinal H).
      set (n := VSet.cardinal s'); clearbody n.
      revert x y s s' H. induction n.
      - reflexivity.
      - cbn. intros x y s s' H. erewrite map_ext.
        erewrite VSetFact.mem_m. 2: reflexivity. 2: eassumption.
        reflexivity.
        intros [m z]; cbn. erewrite IHn.
        reflexivity. now eapply VSetFact.remove_m.
    Qed.

    Lemma lsp0_spec_le {s x y} (p : SPath s x y)
      : (Some (sweight p) <= lsp0 s x y)%nbar.
    Proof using Type.
      induction p; rewrite lsp0_eq; simpl.
      - destruct (V.eq_dec x x); [|contradiction].
        destruct (VSet.mem x s0); [|cbn; reflexivity].
        match goal with
        | |- (_ <= fold_left ?F _ _)%nbar =>
          assert (XX: (forall l acc, Some 0 <= acc -> Some 0 <= fold_left F l acc)%nbar);
            [|apply XX; cbn; reflexivity]
        end.
        clear; induction l.
        + cbn; trivial.
        + intros acc H; simpl. apply IHl.
          apply max_le'; now left.
      - assert (ee: VSet.mem x s' = true). {
          apply VSet.mem_spec, d. left; reflexivity. }
        rewrite ee. etransitivity.
        eapply (plus_le_compat (Some e.π1) _ (Some (sweight p))).
        reflexivity. eassumption.
        apply Nbar.fold_max_le'.
        right.
        unfold succs. rewrite map_map_compose.
        apply in_map_iff. exists (x, e.π1, y). simpl.
        split.
        + cbn -[lsp0].
          assert (XX: VSet.Equal (VSet.remove x s') s0). {
            clear -d.
            intro a; split; intro Ha.
            * apply VSet.remove_spec in Ha. pose proof (d.p1 a).
              intuition. now symmetry in H2.
            * apply VSet.remove_spec. split.
              apply d. right; assumption.
              intro H. apply proj2 in d. apply d.
              red in H; subst; assumption. }
          rewrite (lsp0_VSet_Equal XX); reflexivity.
        + apply filter_In. split.
          apply InA_In_eq, EdgeSet.elements_spec1. exact e.π2.
          cbn. destruct (V.eq_dec x x); [reflexivity|contradiction].
    Qed.

    Lemma lsp0_spec_eq {s x y} n
      : lsp0 s x y = Some n -> exists p : SPath s x y, sweight p = n.
    Proof using Type.
      set (c := VSet.cardinal s). assert (e: VSet.cardinal s = c) by reflexivity.
      clearbody c; revert s e x y n.
      induction c using Wf_nat.lt_wf_ind.
      rename H into IH.
      intros s e x y n H.
      rewrite lsp0_eq in H; cbn -[lsp0] in H.
      case_eq (VSet.mem x s); intro Hx; rewrite Hx in H.
      - apply fold_max_In in H. destruct H.
        + destruct (V.eq_dec x y); [|discriminate].
          apply some_inj in H; subst.
          unshelve eexists; constructor.
        + apply in_map_iff in H.
          destruct H as [[x' n'] [H1 H2]].
          case_eq (lsp0 (VSet.remove x s) n' y).
          2: intros ee; rewrite ee in H1; discriminate.
          intros nn ee; rewrite ee in H1.
          eapply IH in ee. 3: reflexivity.
          * destruct ee as [p1 Hp1].
            unfold succs in H2.
            apply in_map_iff in H2.
            destruct H2 as [[[x'' n''] y''] [H2 H2']]; cbn in H2.
            inversion H2; subst; clear H2.
            apply filter_In in H2'; destruct H2' as [H2 H2']; cbn in H2'.
            destruct (V.eq_dec x'' x); [subst|discriminate]; clear H2'.
            unshelve eexists. econstructor.
            3: eassumption.
            -- split. 2: apply VSetFact.remove_1; reflexivity.
               apply VSetProp.Add_remove.
               apply VSet.mem_spec; assumption.
            -- eexists.
               apply (EdgeSet.elements_spec1 _ _).p1, InA_In_eq; eassumption.
            -- cbn. now apply some_inj in H1.
          * subst. clear -Hx. apply VSet.mem_spec in Hx.
            apply VSetProp.remove_cardinal_1 in Hx. lia.
      - destruct (V.eq_dec x y); [|discriminate].
        apply some_inj in H; subst. unshelve eexists; constructor.
    Qed.

    Lemma lsp0_spec_eq0 {s x} n
      : lsp0 s x x = Some n -> 0 <= n.
    Proof using Type.
      intros lspeq.
      generalize (lsp0_spec_le (spath_refl s x)).
      rewrite lspeq. simpl. auto.
    Qed.

    Lemma correct_labelling_PathOf l (Hl : correct_labelling l)
      : forall x y (p : PathOf x y), Z.of_nat (l x) + weight p <= Z.of_nat (l y).
    Proof using Type.
      induction p. cbn; lia.
      apply proj2 in Hl.
      specialize (Hl (x, e.π1, y) e.π2). cbn in *; lia.
    Qed.

    Lemma correct_labelling_lsp {x y n} (e : lsp x y = Some n) :
      forall l, correct_labelling l -> Z.of_nat (l x) + n <= Z.of_nat (l y).
    Proof using Type.
      eapply lsp0_spec_eq in e as [p Hp].
      intros l Hl; eapply correct_labelling_PathOf with (p:= to_pathOf p) in Hl.
      now rewrite <- sweight_weight, Hp in Hl.
    Qed.

    Lemma acyclic_labelling l : correct_labelling l -> acyclic_no_loop.
    Proof using Type.
      intros Hl x p.
      specialize (correct_labelling_PathOf l Hl x x p); lia.
    Qed.

    Lemma lsp0_triangle_inequality {HG : acyclic_no_loop} s x y1 y2 n
          (He : EdgeSet.In (y1, n, y2) (E G))
          (Hy : VSet.In y1 s)
      : (lsp0 s x y1 + Some n <= lsp0 s x y2)%nbar.
    Proof using Type.
      case_eq (lsp0 s x y1); [|cbn; trivial].
      intros m Hm.
      apply lsp0_spec_eq in Hm.
      destruct Hm as [p Hp].
      case_eq (split' p).
      intros p1 p2 Hp12.
      pose proof (weight_split' p) as H.
      rewrite Hp12 in H; cbn in H.
      etransitivity.
      2: unshelve eapply (lsp0_spec_le (add_end p1 (n; He) _)).
      subst; rewrite weight_add_end; cbn.
      pose proof (sweight_weight p2) as HH.
      red in HG. specialize (HG _ (to_pathOf p2)). lia.
      now apply DisjointAdd_remove1.
    Qed.

    Definition is_nonpos n :=
      match n with
      | Some z => (z <=? 0)
      | None => false
      end.

    Lemma is_nonpos_spec n : is_nonpos n <-> exists z, n = Some z /\ z <= 0.
    Proof using Type.
      unfold is_nonpos.
      split.
      - destruct n; try intuition congruence.
        intros le. eapply Z.leb_le in le. exists z; intuition eauto.
      - intros [z [-> le]]. now eapply Z.leb_le.
    Qed.

    Lemma is_nonpos_nbar n : is_nonpos n -> (n <= Some 0)%nbar.
    Proof using Type.
      now intros [z [-> le]]%is_nonpos_spec.
    Qed.

    Definition lsp0_sub {s s' x y}
      : VSet.Subset s s' -> (lsp0 s x y <= lsp0 s' x y)%nbar.
    Proof using Type.
      case_eq (lsp0 s x y); [|cbn; trivial].
      intros n Hn Hs.
      apply lsp0_spec_eq in Hn; destruct Hn as [p Hp]; subst.
      rewrite <- (weight_SPath_sub Hs p).
      apply lsp0_spec_le.
    Qed.

    Definition snodes_Subset {s x y} (p : SPath s x y)
      : VSet.Subset (snodes p) s.
    Proof using Type.
      induction p; cbn.
      - apply VSetProp.subset_empty.
      - apply VSetProp.subset_add_3.
        apply d. left; reflexivity.
        etransitivity. eassumption.
        eapply DisjointAdd_Subset; eassumption.
    Qed.

    Definition reduce {s x y} (p : SPath s x y)
      : SPath (snodes p) x y.
    Proof.
      induction p; cbn.
      - constructor.
      - econstructor; try eassumption.
        apply DisjointAdd_add2.
        intro Hx; apply d. eapply snodes_Subset.
        eassumption.
    Defined.


    Definition simplify2 {x z} (p : PathOf x z) :  SPath (nodes p) x z.
    Proof.
      induction p; cbn.
      - constructor.
      - case_eq (VSet.mem x (snodes IHp)); intro Hx.
        + apply VSetFact.mem_2 in Hx.
          eapply SPath_sub. 2: exact (split _ _ (left Hx)).2.
          apply VSetProp.subset_add_2; reflexivity.
        + eapply SPath_sub. shelve.
          econstructor. 2: eassumption. 2: exact (reduce IHp).
          eapply DisjointAdd_add2. now apply VSetFact.not_mem_iff.
          Unshelve.
          apply VSetFact.add_s_m. reflexivity.
          apply snodes_Subset.
    Defined.

    Lemma weight_reduce {s x y} (p : SPath s x y)
      : sweight (reduce p) = sweight p.
    Proof using Type.
      induction p; simpl; intuition.
    Qed.

    Opaque split reduce SPath_sub.

    Lemma weight_simplify2 {HG : acyclic_no_loop} {x z} (p : PathOf x z)
      : weight p <= sweight (simplify2 p).
    Proof using Type.
      induction p.
      - reflexivity.
      - simpl.
        set (F0 := @VSetFact.mem_2 (snodes (simplify2 p)) x); clearbody F0.
        set (F1 := VSetFact.not_mem_iff (snodes (simplify2 p)) x); clearbody F1.
        destruct (VSet.mem x (snodes (simplify2 p))).
        + rewrite weight_SPath_sub.
          pose proof (@weight_split _ _ _ (simplify2 p))
               x (left (F0 (eq_refl))).
          set (q := split (simplify2 p) x (left (F0 (eq_refl)))) in *.
          destruct q as [q1 q2]; cbn in *.
          assert (sweight q1 + e.π1 <= 0); [|].
          specialize (HG _ (pathOf_step e (to_pathOf q1))). cbn in HG.
          rewrite <- sweight_weight in HG. lia.
          transitivity (e.π1 + sweight (simplify2 p)); [|lia]. rewrite <- H. lia.
        + rewrite weight_SPath_sub. cbn.
          rewrite weight_reduce; intuition.
    Qed.

    Context {HI : invariants}.

    Lemma nodes_subset {x y} (p : PathOf x y)
      : VSet.Subset (nodes p) (V G).
    Proof using HI.
      induction p; cbn.
      apply VSetProp.subset_empty.
      apply VSetProp.subset_add_3; [|assumption].
      apply (edges_vertices _ e.π2).
    Qed.

    Definition simplify2' {x z} (p : PathOf x z) :  SPath (V G) x z.
    Proof using G HI.
      eapply SPath_sub. 2: exact (simplify2 p).
      apply nodes_subset.
    Defined.

    Lemma weight_simplify2' {HG : acyclic_no_loop} {x z} (p : PathOf x z)
      : weight p <= sweight (simplify2' p).
    Proof using Type.
      unfold simplify2'.
      unshelve erewrite weight_SPath_sub.
      eapply weight_simplify2.
    Qed.

    Lemma lsp_s {HG : acyclic_no_loop} x (Hx : VSet.In x (V G))
      : exists n, lsp (s G) x = Some n /\ 0 <= n.
    Proof using G HI.
      case_eq (lsp (s G) x).
      - intros n H; eexists; split; [reflexivity|].
        destruct (source_pathOf _ Hx) as [[p [w]]].
        pose proof (lsp0_spec_le (simplify2' p)).
        unfold lsp in H. rewrite H in H0.
        simpl in H0.
        transitivity (weight p); auto.
        etransitivity; eauto. eapply weight_simplify2'.
      - intro e.
        destruct (source_pathOf x Hx) as [[p [w]]].
        pose proof (lsp0_spec_le (simplify2' p)) as X.
        unfold lsp in e; rewrite e in X. inversion X.
    Qed.

    Lemma SPath_In {s x y} (p : SPath s x y)
    : sweight p <> 0 -> VSet.In x s.
    Proof using Type.
      destruct p. simpl. lia.
      intros _. apply d. left; reflexivity.
    Qed.

    Lemma SPath_In' {s x y} (p : SPath s x y) (H : VSet.In x (V G)) :
      VSet.In y (V G).
    Proof using G HI.
      induction p. simpl; auto.
      apply IHp. destruct e.
      now specialize (edges_vertices _ i).
    Qed.

    Lemma PathOf_In {x y} : VSet.In y (V G) -> PathOf x y -> VSet.In x (V G).
    Proof using G HI.
      intros hin p; induction p; auto.
      destruct e as [? ine].
      now eapply edges_vertices in ine.
    Qed.

    Lemma acyclic_lsp0_xx {HG : acyclic_no_loop} s x
      : lsp0 s x x = Some 0.
    Proof using Type.
      pose proof (lsp0_spec_le (spath_refl s x)) as H; cbn in H.
      case_eq (lsp0 s x x); [|intro e; rewrite e in H; cbn in H; lia].
      intros n Hn.
      pose proof (lsp0_spec_eq0 _ Hn).
      apply lsp0_spec_eq in Hn.
      destruct Hn as [p Hp]. rewrite sweight_weight in Hp.
      red in HG.
      specialize (HG _ (to_pathOf p)). subst n. f_equal. lia.
    Qed.

    (* We don't care about the default value here: lsp is defined everywhere starting from the source. *)
    Definition to_label (z : option Z) :=
      match z with
      | Some (Zpos p) => Pos.to_nat p
      | _ => 0%nat
      end.

    Lemma Z_of_to_label (z : Z) :
      Z.of_nat (to_label (Some z)) = if 0 <=? z then z else 0.
    Proof using Type.
      simpl. destruct z; auto. simpl.
      apply Z_of_pos_alt.
    Qed.

    Lemma Z_of_to_label_s {HG : acyclic_no_loop} x :
      VSet.In x (V G) ->
      exists n, lsp (s G) x = Some n /\
        0 <= n /\ (Z.of_nat (to_label (lsp (s G) x))) = n.
    Proof using G HI.
      intros inx.
      destruct (lsp_s x inx) as [m [Hm Hpos]].
      rewrite Hm. eexists; split; auto. split; auto.
      rewrite Z_of_to_label.
      eapply Z.leb_le in Hpos. now rewrite Hpos.
    Qed.

    Lemma lsp_correctness {HG : acyclic_no_loop} :
        correct_labelling (fun x => to_label (lsp (s G) x)).
    Proof using G HI.
      split.
      - unfold lsp. now rewrite acyclic_lsp0_xx.
      - intros [[x n] y] He; cbn.
        simple refine (let H := lsp0_triangle_inequality
                                  (V G) (s G) x y n He _
                       in _); [|clearbody H].
        apply (edges_vertices _ He).
        fold lsp in H. revert H.
        destruct (Z_of_to_label_s x) as [xl [eq [pos ->]]]; rewrite ?eq.
        + apply (edges_vertices _ He).
        + destruct (Z_of_to_label_s y) as [yl [eq' [ylpos ->]]]; rewrite ?eq'.
          * apply (edges_vertices _ He).
          * now simpl.
    Qed.

    Lemma lsp_codistance {HG : acyclic_no_loop} x y z
      : (lsp x y + lsp y z <= lsp x z)%nbar.
    Proof using HI.
      case_eq (lsp x y); [|cbn; trivial]. intros n Hn.
      case_eq (lsp y z); [|cbn; trivial]. intros m Hm.
      destruct (lsp0_spec_eq _ Hn) as [p1 Hp1].
      destruct (lsp0_spec_eq _ Hm) as [p2 Hp2].
      pose proof (lsp0_spec_le (simplify2' (concat (to_pathOf p1) (to_pathOf p2))))
        as XX.
      epose proof (weight_simplify2' (concat (to_pathOf p1) (to_pathOf p2))).
      unshelve erewrite weight_concat, <- !sweight_weight in H;
        try assumption.
      cbn in H; erewrite Hp1, Hp2 in H.
      simpl. etransitivity; eauto. simpl. eauto.
    Qed.

    (* The two largest simple pathOf between nodes in both directions bound each other. *)
    Lemma lsp_sym {HG : acyclic_no_loop} {x y n} :
      lsp x y = Some n ->
      (lsp y x <= Some (-n))%nbar.
    Proof using Type.
      intros Hn.
      destruct (lsp0_spec_eq _ Hn) as [p Hp].
      destruct (lsp y x) eqn:lspyx.
      2:simpl; auto.
      epose proof (lsp0_spec_eq _ lspyx) as [pi Hpi].
      clear Hn lspyx. rewrite -Hp -Hpi /=.
      epose proof (weight_simplify (to_pathOf pi) p (reflexivity _)).
      destruct simplify as [h loop].
      simpl in H.
      move: (HG _ (to_pathOf loop)).
      rewrite -sweight_weight.
      rewrite -sweight_weight Hp Hpi in H.
      rewrite Hp Hpi.
      destruct (Z.ltb 0 (z + n)) eqn:ltb.
      eapply Z.ltb_lt in ltb. specialize (H ltb). lia.
      eapply Z.ltb_nlt in ltb.
      intros wl.
      lia.
    Qed.

    Lemma le_Some_lsp {n x y} : (Some n <= lsp x y)%nbar ->
      exists k, lsp x y = Some k /\ n <= k.
    Proof using Type.
      destruct lsp eqn:xy.
      simpl. intros. eexists; split; eauto.
      simpl; now intros [].
    Qed.

    (* There can be no universe lower than the source: all pathOf to the source have null or
      negative weight. *)
    Lemma source_bottom {HG : acyclic_no_loop} {x} (p : PathOf x (s G)) : weight p <= 0.
    Proof using HI.
      unshelve epose proof (PathOf_In _ p).
      eapply source_vertex.
      destruct (lsp_s _ H) as [lx [lsx w]].
      etransitivity; [apply (weight_simplify2' p)|].
      set (sp := simplify2' p).
      epose proof (lsp0_spec_le sp).
      eapply le_Some_lsp in H0 as [xs [lxs wxs]].
      generalize (lsp_codistance x (s G) x).
      rewrite lxs lsx /lsp acyclic_lsp0_xx /=. lia.
    Qed.

    Lemma lsp_to_s {HG : acyclic_no_loop} {x} (Hx : VSet.In x (V G)) {n}
      : lsp x (s G) = Some n -> n <= 0.
    Proof using HI.
      case_eq (lsp x (s G)).
      - intros z H [= <-].
        destruct (lsp0_spec_eq _ H).
        pose proof (source_bottom (to_pathOf x0)).
        rewrite <- sweight_weight in H1. congruence.
      - intro e. discriminate.
    Qed.

    Lemma lsp_xx_acyclic
      : VSet.For_all (fun x => lsp x x = Some 0) (V G) -> acyclic_no_loop'.
    Proof using G HI.
      intros H. intros x [p Hp]. assert (hw: 0 < weight p + sweight ((spath_refl (V G) x))) by (simpl; lia).
      simple refine (let Hq := weight_simplify p (spath_refl (V G) _)
                                               _ hw
                     in _).
      + exact (V G).
      + etransitivity. apply VSetProp.union_sym.
        etransitivity. apply VSetProp.union_subset_equal.
        apply nodes_subset. reflexivity.
      + match goal with
        | _ : 0 < sweight ?qq.π2 |- _ => set (q := qq) in *; clearbody Hq
        end.
        destruct q as [x' q]; cbn in Hq.
        assert (Some (sweight q) <= Some 0)%nbar. {
          erewrite <- H. eapply lsp0_spec_le.
          eapply (SPath_In q). lia. }
        cbn in H0; lia.
    Defined.

    Lemma VSet_Forall_reflect P f (Hf : forall x, reflect (P x) (f x)) s
      : reflect (VSet.For_all P s) (VSet.for_all f s).
    Proof using G HI.
      apply iff_reflect. etransitivity.
      2: apply VSetFact.for_all_iff.
      2: intros x y []; reflexivity.
      apply iff_forall; intro x.
      apply iff_forall; intro Hx.
      now apply reflect_iff.
    Qed.

    Lemma reflect_logically_equiv {A B} (H : A <-> B) f
      : reflect B f -> reflect A f.
    Proof using Type.
      destruct 1; constructor; intuition.
    Qed.

    Definition is_acyclic := VSet.for_all (fun x => match lsp x x with
                                                 | Some 0 => true
                                                 | _ => false
                                                 end) (V G).


    (** ** Main results about acyclicity *)

    Lemma acyclic_caract1
      : acyclic_no_loop <-> exists l, correct_labelling l.
    Proof using G HI.
      split.
      intro HG; eexists. eapply (lsp_correctness).
      intros [l Hl]; eapply acyclic_labelling; eassumption.
    Defined.

    Lemma acyclic_caract2 :
      acyclic_no_loop <-> (VSet.For_all (fun x => lsp x x = Some 0) (V G)).
    Proof using G HI.
      split.
      - intros HG x Hx. unshelve eapply acyclic_lsp0_xx.
      - intros H. apply acyclic_no_loop_loop'.
        now eapply lsp_xx_acyclic.
    Defined.

    (* Lemma acyclic_caract3 *)
    (*   : acyclic_no_loop <-> acyclic_well_founded. *)
    (* Proof. *)
    (*   split. *)
    (*   intro. eapply acyclic_labelling. *)
    (*   now eapply lsp_correctness. *)
    (*   apply acyclic_wf_no_loop. *)
    (* Defined. *)

    Lemma is_acyclic_spec : is_acyclic <-> acyclic_no_loop.
    Proof using HI.
      symmetry. etransitivity. eapply acyclic_caract2.
      etransitivity. 2: eapply VSetFact.for_all_iff.
      2: now intros x y [].
      apply iff_forall; intro x.
      apply iff_forall; intro Hx.
      split. now intros ->.
      destruct lsp as [[]|]; try congruence.
    Qed.

    Lemma Zle_opp {n m} : - n <= m <-> - m <= n.
    Proof using Type. lia. Qed.

    Lemma Zle_opp' {n m} : n <= m <-> - m <= - n.
    Proof using Type. lia. Qed.

    Lemma lsp_xx {HG : acyclic_no_loop} {x} : lsp x x = Some 0.
    Proof using Type.
      rewrite /lsp.
      now rewrite acyclic_lsp0_xx.
    Qed.

    Definition edge_pathOf {e} : EdgeSet.In e (E G) -> PathOf e..s e..t.
    Proof.
      intros hin.
      eapply (pathOf_step (y := e..t)). exists e..w. destruct e as [[s w] t].
      simpl in *. apply hin. constructor.
    Defined.

    Lemma Z_of_to_label_pos x : 0 <= x -> Z.of_nat (to_label (Some x)) = x.
    Proof using Type.
      intros le.
      rewrite Z_of_to_label.
      destruct (Z.leb_spec 0 x); auto. lia.
    Qed.

    Lemma to_label_max x y : (Some 0 <= x)%nbar -> to_label (max x y) = Nat.max (to_label x) (to_label y).
    Proof using Type.
      destruct x; intros H; simpl in H; auto. 2:elim H.
      eapply Nat2Z.inj.
      rewrite Nat2Z.inj_max.
      destruct y; cbn -[to_label].
      rewrite Z_of_to_label_pos; try lia.
      rewrite Z_of_to_label_pos. lia.
      rewrite Z_of_to_label.
      destruct (Z.leb_spec 0 z0); lia.
      rewrite Z_of_to_label_pos; try lia.
      simpl. lia.
    Qed.

    Lemma lsp_from_source {HG : acyclic_no_loop} {x} {n} : lsp (s G) x = Some n -> 0 <= n.
    Proof using HI.
      intros H.
      assert (VSet.In x (V G)).
      destruct (lsp0_spec_eq _ H).
      apply (SPath_In' x0). eapply HI.
      destruct (lsp_s _ H0) as [n' [lspeq w]].
      rewrite H in lspeq. congruence.
    Qed.

    Lemma lsp_to_source {HG : acyclic_no_loop} {x z} : lsp x (s G) = Some z -> z <= 0.
    Proof using HI.
      intros h.
      destruct (lsp0_spec_eq z h).
      pose proof (source_bottom (to_pathOf x0)).
      rewrite -sweight_weight in H0. lia.
    Qed.

    Lemma lsp_source_max {HG : acyclic_no_loop} {x y} : VSet.In x (V G) -> VSet.In y (V G) ->
       (lsp y x <= lsp (s G) x)%nbar.
    Proof using HI.
      intros inx iny.
      destruct (Z_of_to_label_s x) as [zl [eq [pos zof]]]; eauto.
      rewrite eq. simpl.
      destruct (lsp y x) eqn:yx.
      simpl.
      pose proof (lsp_codistance (s G) y x).
      rewrite eq yx in H. simpl in *.
      destruct (lsp_s y iny) as [ly [lspy neg]].
      rewrite lspy in H. simpl in H. lia.
      now simpl.
    Qed.

    Lemma is_acyclic_correct : reflectProp acyclic_no_loop is_acyclic.
    Proof using HI.
      eapply reflect_reflectProp, reflect_logically_equiv.
      eapply acyclic_caract2.
      apply VSet_Forall_reflect; intro x.
      destruct (lsp x x). destruct z. constructor; reflexivity.
      all: constructor; discriminate.
    Qed.
  End graph.

  (* Unused as far as I can tell + introduce an equality constraint and not inequality.. *)
  (* Definition add_edges G e := *)
  (*   add_edge (add_edge G e) (opp_edge e). *)
  Arguments sweight {G s x y}.
  Arguments weight {G x y}.

  Module Subgraph1.
    Section graph2.
    Context (G : t) {HI : invariants G} {HG : acyclic_no_loop G}.
    Context (y_0 x_0 : V.t) (Vx : VSet.In x_0 (V G))
              (Vy : VSet.In y_0 (V G))
              (K : Z)
              (Hxs : lsp G x_0 y_0 = Some K).

    Local Definition G' : t
      := (V G, EdgeSet.add (y_0, - K, x_0) (E G), s G).

    Definition to_G' {u v} (q : PathOf G u v) : PathOf G' u v.
    Proof.
      clear -q.
      induction q; [constructor|].
      econstructor. 2: eassumption.
      exists e.π1. cbn. apply EdgeSet.add_spec; right. exact e.π2.
    Defined.

    Lemma to_G'_weight {u v} (p : PathOf G u v)
      : weight (to_G' p) = weight p.
    Proof using Type.
      clear.
      induction p. reflexivity.
      simpl. now rewrite IHp.
    Qed.

    Opaque Edge.eq_dec.


    Definition from_G'_path {u v} (q : PathOf G' u v)
      : PathOf G u v + (PathOf G u y_0 * PathOf G x_0 v).
    Proof.
      clear -q. induction q.
      - left; constructor.
      - induction (Edge.eq_dec (y_0, -K, x_0) (x, e.π1, y)) as [XX|XX].
        + right. split.
          * rewrite (fst_eq (fst_eq XX)); constructor.
          * destruct IHq as [IHq|IHq].
            -- now rewrite (snd_eq XX).
            -- exact IHq.2.
        + induction IHq as [IHq|IHq].
          * left. econstructor; try eassumption.
            exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
          * right. split.
            -- econstructor; try eassumption.
                2: exact IHq.1.
                exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
            -- exact IHq.2.
    Defined.

    Lemma from_G'_path_weight {u v} (q : PathOf G' u v)
      : match from_G'_path q with
        | inl q' => weight q = weight q'
        | inr (q1, q2) =>
          weight q <= weight q1 - K + weight q2
        end.
    Proof using HG HI Hxs.
      clear -HI HG Hxs.
      induction q.
      - reflexivity.
      - simpl.
        destruct (Edge.eq_dec (y_0, - K, x_0) (x, e.π1, y)) as [XX|XX]; simpl.
        + destruct (fst_eq (fst_eq XX)). simpl.
          inversion XX.
          destruct (from_G'_path q) as [q'|[q1 q2]]; simpl.
          * destruct (snd_eq XX); cbn.
            destruct e as [e He]; cbn in *. lia.
          * subst y.
            transitivity (-K + weight q1 - K + weight q2). lia.
            epose proof (lsp0_spec_le G (simplify2' G q1)).
            unfold lsp in Hxs; rewrite Hxs /= in H.
            pose proof (weight_simplify2' G q1). lia.
        + destruct (from_G'_path q) as [q'|[q1 q2]]; simpl.
          * lia.
          * lia.
    Qed.

    Definition from_G' {S u v} (q : SPath G' S u v)
      : SPath G S u v + (SPath G S u y_0 * SPath G S x_0 v).
    Proof.
      clear -q. induction q.
      - left; constructor.
      - induction (Edge.eq_dec (y_0, - K, x_0) (x, e.π1, y)) as [XX|XX].
        + right. split.
          * rewrite (fst_eq (fst_eq XX)); constructor.
          * eapply SPath_sub.
            eapply DisjointAdd_Subset; eassumption.
            induction IHq as [IHq|IHq].
            -- now rewrite (snd_eq XX).
            -- exact IHq.2.
        + induction IHq as [IHq|IHq].
          * left. econstructor; try eassumption.
            exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
          * right. split.
            -- econstructor; try eassumption.
                2: exact IHq.1.
                exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
            -- eapply SPath_sub; [|exact IHq.2].
                eapply DisjointAdd_Subset; eassumption.
    Defined.

    Lemma from_G'_weight {S u v} (q : SPath G' S u v)
      : match from_G' q with
        | inl q' => sweight q = sweight q'
        | inr (q1, q2) => sweight q <= sweight q1 - K + sweight q2
        end.
    Proof using HG HI Hxs.
      clear -HI HG Hxs.
      induction q.
      - reflexivity.
      - simpl.
        destruct (Edge.eq_dec (y_0, - K, x_0) (x, e.π1, y)) as [XX|XX]; simpl.
        + destruct (fst_eq (fst_eq XX)). simpl.
          inversion XX. rewrite weight_SPath_sub.
          destruct (from_G' q) as [q'|[q1 q2]]; simpl.
          * destruct (snd_eq XX); cbn.
            destruct e as [e He]; cbn in *; lia.
          * subst y.
            assert (Hle := lsp0_spec_le G (simplify2' G (to_pathOf G q1))).
            unfold lsp in *. rewrite Hxs /= in Hle.
            pose proof (weight_simplify2' G (to_pathOf G q1)).
            rewrite -sweight_weight in H. lia.
        + destruct (from_G' q) as [q'|[q1 q2]]; simpl.
          * lia.
          * rewrite weight_SPath_sub; lia.
    Qed.

    Lemma lsp_pathOf {x y} (p : PathOf G x y) : exists n, lsp G x y = Some n /\ weight p <= n.
    Proof using HG HI.
      pose proof (lsp0_spec_le G (simplify2' G p)) as ineq.
      unfold lsp in *.
      destruct (lsp0 G (V G) x y). eexists; eauto. split; eauto.
      simpl in ineq. epose proof (weight_simplify2' G p). lia.
      now simpl in ineq.
    Qed.

    Global Instance HI' : invariants G'.
    Proof using HI Vx Vy.
      split.
      - cbn. intros e He. apply EdgeSet.add_spec in He; destruct He as [He|He].
        subst; cbn. split; assumption.
        now apply HI.
      - apply HI.
      - intros z Hz. epose proof (source_pathOf G z Hz).
        destruct H as [[p [w]]]. sq. exists (to_G' p).
        sq. now rewrite to_G'_weight.
    Qed.

    Global Instance HG' : acyclic_no_loop G'.
    Proof using HG HI Hxs Vx Vy.
      apply acyclic_caract2. exact _. intros x Hx.
      pose proof (lsp0_spec_le G' (spath_refl G' (V G') x)) as H; cbn in H.
      case_eq (lsp0 G' (V G) x x); [|intro e; rewrite e in H; cbn in H; lia].
      intros m Hm. unfold lsp; cbn; rewrite Hm. rewrite Hm in H.
      simpl in H.
      apply lsp0_spec_eq in Hm.
      destruct Hm as [p Hp]. subst.
      pose proof (from_G'_weight p) as XX.
      destruct (from_G' p).
      - f_equal. rewrite (sweight_weight G s0) in XX.
        specialize (HG _ (to_pathOf G s0)). lia.
      - assert (Hle := lsp0_spec_le G (simplify2' G (concat G (to_pathOf G p0.2) (to_pathOf G p0.1)))).
        destruct p0 as [q1 q2]; simpl in *.
        unfold lsp in *; rewrite -> Hxs in Hle. simpl in Hle.
        epose proof (weight_simplify2' G (concat G (to_pathOf G q2) (to_pathOf G q1))).
        rewrite weight_concat - !sweight_weight in H0. f_equal.
        enough (sweight q1 - K + sweight q2 <= 0). lia.
        lia.
    Qed.

    Lemma lsp_G'_yx : (Some (- K) <= lsp G' y_0 x_0)%nbar.
    Proof using Vy.
      unshelve refine (transport (fun K => (Some K <= _)%nbar) _ (lsp0_spec_le _ _)).
      - eapply spath_one; tas.
        apply EdgeSet.add_spec. now left.
      - cbn. lia.
    Qed.

    Lemma correct_labelling_lsp_G'
      : correct_labelling G (to_label ∘ (lsp G' (s G'))).
    Proof using HG HI Hxs Vx Vy.
      pose proof (lsp_correctness G') as XX.
      split. exact XX.p1.
      intros e He; apply XX; cbn.
      apply EdgeSet.add_spec; now right.
    Qed.

    Definition sto_G' {S u v} (p : SPath G S u v)
      : SPath G' S u v.
    Proof.
      clear -p. induction p.
      - constructor.
      - econstructor; tea. exists e.π1.
        apply EdgeSet.add_spec. right. exact e.π2.
    Defined.


    Lemma sto_G'_weight {S u v} (p : SPath G S u v)
      : sweight (sto_G' p) = sweight p.
    Proof using Type.
      clear.
      induction p. reflexivity.
      simpl. now rewrite IHp.
    Qed.

    Lemma lsp_G'_incr x y : (lsp G x y <= lsp G' x y)%nbar.
    Proof using Type.
      case_eq (lsp G x y); cbn; [|trivial].
      intros kxy Hkxy. apply lsp0_spec_eq in Hkxy.
      destruct Hkxy as [pxy Hkxy].
      etransitivity. 2: eapply (lsp0_spec_le _ (sto_G' pxy)).
      rewrite sto_G'_weight. now rewrite Hkxy.
    Qed.

    Lemma lsp_G'_sx : (lsp G' (s G) y_0 + Some (- K) <= lsp G' (s G) x_0)%nbar.
    Proof using HG HI Hxs Vx Vy.
      etransitivity. 2: eapply lsp_codistance; try exact _.
      apply plus_le_compat_l. apply lsp_G'_yx.
    Qed.

    Lemma lsp_G'_spec_left x :
      lsp G' y_0 x = max (lsp G y_0 x) (Some (- K) + lsp G x_0 x)%nbar.
    Proof using HG HI Hxs Vx Vy.
      apply Nbar.le_antisymm.
      - case_eq (lsp G' y_0 x); [|cbn; trivial].
        intros k Hk.
        apply lsp0_spec_eq in Hk; destruct Hk as [p' Hk].
        subst k.
        generalize (from_G'_weight p').
        destruct (from_G' p') as [p|[p1 p2]].
        + intros ->. apply max_le'. left. apply lsp0_spec_le.
        + intros He. apply max_le'. right.
          pose proof (lsp_pathOf (to_pathOf G p2)) as [x0x [lspx0x wp2]].
          rewrite -sweight_weight in wp2. rewrite lspx0x. simpl.
          pose proof (lsp_pathOf (to_pathOf G p1)) as [y0y0 [lspy0 wp1]].
          rewrite -sweight_weight in wp1. rewrite lsp_xx in lspy0.
          injection lspy0; intros <-. lia.
      - apply max_lub. apply lsp_G'_incr.
        case_eq (lsp G x_0 x); cbn; [intros k Hk|trivial].
        etransitivity.
        2:apply (lsp_codistance G' y_0 x_0 x).
        pose proof (lsp_G'_yx).
        eapply le_Some_lsp in H as [y0x0 [-> w]].
        generalize (lsp_G'_incr x_0 x). rewrite Hk.
        move/le_Some_lsp => [x0x [-> w']]. simpl. lia.
    Qed.
    End graph2.
  End Subgraph1.

  Section subgraph.
    Context (G : t) {HI : invariants G} {HG : acyclic_no_loop G}.

    Section subgraph2.
      Context (y_0 x_0 : V.t) (Vx : VSet.In x_0 (V G))
              (Vy : VSet.In y_0 (V G))
              (Hxs : lsp G x_0 y_0 = None)
              (K : Z).

      Local Definition G' : t
        := (V G, EdgeSet.add (y_0, K, x_0) (E G), s G).

      Definition to_G' {u v} (q : PathOf G u v) : PathOf G' u v.
      Proof.
        clear -q.
        induction q; [constructor|].
        econstructor. 2: eassumption.
        exists e.π1. cbn. apply EdgeSet.add_spec; right. exact e.π2.
      Defined.

      Lemma to_G'_weight {u v} (p : PathOf G u v)
        : weight (to_G' p) = weight p.
      Proof using Type.
        clear.
        induction p. reflexivity.
        simpl. now rewrite IHp.
      Qed.

      Opaque Edge.eq_dec.


      Definition from_G'_path {u v} (q : PathOf G' u v)
        : PathOf G u v + (PathOf G u y_0 * PathOf G x_0 v).
      Proof.
        clear -q. induction q.
        - left; constructor.
        - induction (Edge.eq_dec (y_0, K, x_0) (x, e.π1, y)) as [XX|XX].
          + right. split.
            * rewrite (fst_eq (fst_eq XX)); constructor.
            * destruct IHq as [IHq|IHq].
              -- now rewrite (snd_eq XX).
              -- exact IHq.2.
          + induction IHq as [IHq|IHq].
            * left. econstructor; try eassumption.
              exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
            * right. split.
              -- econstructor; try eassumption.
                  2: exact IHq.1.
                  exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
              -- exact IHq.2.
      Defined.


      Lemma from_G'_path_weight {u v} (q : PathOf G' u v)
        : weight q = match from_G'_path q with
                    | inl q' => weight q'
                    | inr (q1, q2) => weight q1 + K + weight q2
                      end.
      Proof using HI Hxs.
        clear -HI HG Hxs.
        induction q.
        - reflexivity.
        - simpl.
          destruct (Edge.eq_dec (y_0, K, x_0) (x, e.π1, y)) as [XX|XX]; simpl.
          + destruct (fst_eq (fst_eq XX)). simpl.
            inversion XX.
            destruct (from_G'_path q) as [q'|[q1 q2]]; simpl.
            * destruct (snd_eq XX); cbn.
              destruct e as [e He]; cbn in *. lia.
            * subst y. rewrite IHq.
              simple refine (let XX := lsp0_spec_le
                                          G (simplify2' G q1) in _).
              unfold lsp in *. rewrite -> Hxs in XX; inversion XX.
          + destruct (from_G'_path q) as [q'|[q1 q2]]; simpl.
            * lia.
            * lia.
      Qed.

      Definition from_G' {S u v} (q : SPath G' S u v)
        : SPath G S u v + (SPath G S u y_0 * SPath G S x_0 v).
      Proof.
        clear -q. induction q.
        - left; constructor.
        - induction (Edge.eq_dec (y_0, K, x_0) (x, e.π1, y)) as [XX|XX].
          + right. split.
            * rewrite (fst_eq (fst_eq XX)); constructor.
            * eapply SPath_sub.
              eapply DisjointAdd_Subset; eassumption.
              induction IHq as [IHq|IHq].
              -- now rewrite (snd_eq XX).
              -- exact IHq.2.
          + induction IHq as [IHq|IHq].
            * left. econstructor; try eassumption.
              exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
            * right. split.
              -- econstructor; try eassumption.
                  2: exact IHq.1.
                  exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
              -- eapply SPath_sub; [|exact IHq.2].
                  eapply DisjointAdd_Subset; eassumption.
      Defined.

      Lemma from_G'_weight {S u v} (q : SPath G' S u v)
        : sweight q = match from_G' q with
                      | inl q' => sweight q'
                      | inr (q1, q2) => sweight q1 + K + sweight q2
                      end.
      Proof using HI Hxs.
        clear -HI HG Hxs.
        induction q.
        - reflexivity.
        - simpl.
          destruct (Edge.eq_dec (y_0, K, x_0) (x, e.π1, y)) as [XX|XX]; simpl.
          + destruct (fst_eq (fst_eq XX)). simpl.
            inversion XX. rewrite weight_SPath_sub.
            destruct (from_G' q) as [q'|[q1 q2]]; simpl.
            * destruct (snd_eq XX); cbn.
              destruct e as [e He]; cbn in *; lia.
            * subst y.
              simple refine (let XX := lsp0_spec_le
                                          G (simplify2' G (to_pathOf G q1)) in _).
              unfold lsp in *. rewrite -> Hxs in XX; inversion XX.
          + destruct (from_G' q) as [q'|[q1 q2]]; simpl.
            * lia.
            * rewrite weight_SPath_sub; lia.
      Qed.

      Lemma lsp_pathOf {x y} (p : PathOf G x y) : exists n, lsp G x y = Some n.
      Proof using HI.
        pose proof (lsp0_spec_le G (simplify2' G p)) as ineq.
        unfold lsp in *.
        destruct (lsp0 G (V G) x y). eexists; eauto.
        now simpl in ineq.
      Qed.

      Global Instance HI' : invariants G'.
      Proof using HI Vx Vy.
        split.
        - cbn. intros e He. apply EdgeSet.add_spec in He; destruct He as [He|He].
          subst; cbn. split; assumption.
          now apply HI.
        - apply HI.
        - intros z Hz. epose proof (source_pathOf G z Hz).
          destruct H as [[p [w]]]. sq. exists (to_G' p).
          sq. now rewrite to_G'_weight.
      Qed.

      Global Instance HG' : acyclic_no_loop G'.
      Proof using HG HI Hxs Vx Vy.
        apply acyclic_caract2. exact _. intros x Hx.
        pose proof (lsp0_spec_le G' (spath_refl G' (V G') x)) as H; cbn in H.
        case_eq (lsp0 G' (V G) x x); [|intro e; rewrite e in H; cbn in H; lia].
        intros m Hm. unfold lsp; cbn; rewrite Hm. rewrite Hm in H.
        simpl in H.
        apply lsp0_spec_eq in Hm.
        destruct Hm as [p Hp]. subst.
        pose proof (from_G'_weight p) as XX.
        destruct (from_G' p).
        - f_equal. rewrite (sweight_weight G s0) in XX.
          specialize (HG _ (to_pathOf G s0)). lia.
        - simple refine (let XX := lsp0_spec_le
            G (simplify2' G (concat G (to_pathOf G p0.2) (to_pathOf G p0.1))) in _).
          unfold lsp in *; rewrite -> Hxs in XX; inversion XX.
      Qed.

      Lemma lsp_G'_yx : (Some K <= lsp G' y_0 x_0)%nbar.
      Proof using Vy.
        unshelve refine (transport (fun K => (Some K <= _)%nbar) _ (lsp0_spec_le _ _)).
        - eapply spath_one; tas.
          apply EdgeSet.add_spec. now left.
        - cbn. lia.
      Qed.

      Lemma lsp_G'_sx : (lsp G' (s G) y_0 + Some K <= lsp G' (s G) x_0)%nbar.
      Proof using HG HI Hxs Vx Vy.
        etransitivity. 2: eapply lsp_codistance; try exact _.
        apply plus_le_compat_l. apply lsp_G'_yx.
      Qed.

      Lemma correct_labelling_lsp_G'
        : correct_labelling G (to_label ∘ (lsp G' (s G'))).
      Proof using HG HI Hxs Vx Vy.
        pose proof (lsp_correctness G') as XX.
        split. exact XX.p1.
        intros e He; apply XX; cbn.
        apply EdgeSet.add_spec; now right.
      Qed.

      Definition sto_G' {S u v} (p : SPath G S u v)
        : SPath G' S u v.
      Proof.
        clear -p. induction p.
        - constructor.
        - econstructor; tea. exists e.π1.
          apply EdgeSet.add_spec. right. exact e.π2.
      Defined.


      Lemma sto_G'_weight {S u v} (p : SPath G S u v)
        : sweight (sto_G' p) = sweight p.
      Proof using Type.
        clear.
        induction p. reflexivity.
        simpl. now rewrite IHp.
      Qed.

      Lemma lsp_G'_incr x y : (lsp G x y <= lsp G' x y)%nbar.
      Proof using Type.
        case_eq (lsp G x y); cbn; [|trivial].
        intros kxy Hkxy. apply lsp0_spec_eq in Hkxy.
        destruct Hkxy as [pxy Hkxy].
        etransitivity. 2: eapply (lsp0_spec_le _ (sto_G' pxy)).
        rewrite sto_G'_weight. now rewrite Hkxy.
      Qed.

      Lemma lsp_G'_spec_left x :
        lsp G' y_0 x = max (lsp G y_0 x) (Some K + lsp G x_0 x)%nbar.
      Proof using HG HI Hxs Vy.
        apply Nbar.le_antisymm.
        - case_eq (lsp G' y_0 x); [|cbn; trivial].
          intros k Hk.
          apply lsp0_spec_eq in Hk; destruct Hk as [p' Hk].
          subst k.
          rewrite (from_G'_weight p').
          destruct (from_G' p') as [p|[p1 p2]].
          + apply max_le'. left. apply lsp0_spec_le.
          + apply max_le'. right.
            apply (plus_le_compat (Some (sweight p1 + K)) _ (Some (sweight p2))).
            * cbn. rewrite sweight_weight.
              specialize (HG _ (to_pathOf G p1)). simpl in *.
              assert (forall x n, n <= 0 -> n + x <= x). lia. apply H. auto.
            * apply lsp0_spec_le.
        - apply max_lub. apply lsp_G'_incr.
          case_eq (lsp G x_0 x); cbn; [intros k Hk|trivial].
          apply lsp0_spec_eq in Hk. destruct Hk as [p Hk].
          unshelve refine (transport (fun K => (Some K <= _)%nbar)
                                      _ (lsp0_spec_le _ _)).
          eapply SPath_sub. shelve.
          pose (p' := sto_G' p).
          unshelve econstructor.
          + exact (snodes G' p').
          + shelve.
          + apply DisjointAdd_add2.
            intro HH. eapply left, split in HH.
            destruct HH as [p1 _].
            apply from_G' in p1. destruct p1 as [p1|[p1 p2]].
            all: epose proof (lsp0_spec_le _ (SPath_sub _ _ p1)) as HH;
              unfold lsp in Hxs; now erewrite Hxs in HH.
          + exists K. apply EdgeSet.add_spec. now left.
          + exact (reduce _ p').
          + rewrite weight_SPath_sub. cbn.
            now rewrite weight_reduce sto_G'_weight Hk.
          Unshelve.
          2-3: now apply VSetProp.subset_remove_3.
          apply VSetProp.subset_add_3. assumption.
          apply snodes_Subset.
      Qed.
    End subgraph2.

    Lemma SPath_sets {s x y} (p : SPath G s x y)
      : x = y \/ VSet.In x s.
    Proof using Type.
      induction p. left; auto.
      destruct IHp; subst. right.
      destruct d.
      apply H. left; auto.
      right. apply d. left; auto.
    Qed.

    Arguments pathOf_refl {G x}.
    Arguments pathOf_step {G x y z}.

    Fixpoint PathOf_add_end {x y z} (p : PathOf G x y) : EdgeOf G y z -> PathOf G x z :=
      match p with
      | pathOf_refl => fun e => pathOf_step e pathOf_refl
      | pathOf_step e' p' => fun e => pathOf_step e' (PathOf_add_end p' e)
      end.

    Lemma PathOf_add_end_weight {x y z} (p : PathOf G x y) (e : EdgeOf G y z) : weight (PathOf_add_end p e) = weight p + e.π1.
    Proof using Type.
      induction p; simpl; auto. lia.
      rewrite IHp. lia.
    Qed.

    Lemma negbe {b} : ~~ b <-> (~ b).
    Proof using Type.
      intuition try congruence.
      now rewrite H0 in H.
      destruct b; simpl; auto.
    Qed.

    Lemma In_nodes_app_end {x y z} (p : PathOf G x y) (e : EdgeOf G y z) i :
      VSet.In i (nodes G (PathOf_add_end p e)) ->
      VSet.In i (nodes G p) \/ i = y.
    Proof using HI.
      induction p; simpl; try sets.
      rewrite VSet.add_spec.
      intros []; subst.
      - sets.
      - specialize (IHp _ H). sets.
    Qed.

    Lemma pathOf_add_end_simpl {x y z} (p : PathOf G x y) (e : EdgeOf G y z) :
      is_simple _ p -> ~~ VSet.mem y (nodes G p) -> is_simple _ (PathOf_add_end p e).
    Proof using HI.
      induction p; simpl; auto.
      move/andP => [nmen iss].
      specialize (IHp e iss). intros Hm%negbe.
      rewrite andb_and. split; auto.
      apply negbe. intro.
      apply VSet.mem_spec in H.
      apply Hm. eapply In_nodes_app_end in H as [inn | ->].
      eapply negbe in nmen. now elim nmen; apply VSet.mem_spec.
      apply VSet.mem_spec. sets.
      eapply IHp. apply negbe => nmem. eapply VSet.mem_spec in nmem.
      eapply Hm. eapply VSet.mem_spec, VSet.add_spec. sets.
    Qed.


    Lemma leq_vertices_caract0 {n x y} (Vy : VSet.In y (V G)) :
      leq_vertices G n x y <-> (Some n <= lsp G x y)%nbar.
    Proof.
      split; intro Hle.
      - assert (Vx : VSet.In x (V G)). {
          case_eq (VSet.mem x (V G)); intro Vx; [now apply VSet.mem_spec in Vx|].
          apply False_rect. apply VSetFact.not_mem_iff in Vx.
          pose (K := (if (n <=? 0)%Z then (Z.to_nat (Z.of_nat (to_label (lsp G (s G) y)) - n)) + 1 else to_label (lsp G (s G) y))%nat).
          pose (l := fun z => if V.eq_dec z x then K
                           else to_label (lsp G (s G) z)).
          unshelve refine (let XX := Hle l _ in _); subst l K.
          * split.
            -- destruct (V.eq_dec (s G) x).
               apply False_rect. apply Vx. subst; apply HI.
               now apply lsp_correctness.
            -- intros e H.
               destruct (V.eq_dec e..s x).
               apply False_rect, Vx; subst; now apply HI.
               destruct (V.eq_dec e..t x).
               apply False_rect, Vx; subst; now apply HI.
               now apply lsp_correctness.
          * clearbody XX; cbn in XX.
            destruct (V.eq_dec x x) as [Hx|Hx]; [|now apply Hx].
            destruct (V.eq_dec y x) as [Hy|Hy].
            now subst.
            pose proof (lsp_correctness G).
            specialize (Hle _ H). simpl in Hle.
            destruct (Z_of_to_label_s G y) as [zl [eq [pos zof]]]; eauto.
            rewrite zof in XX, Hle.
            destruct (Z.leb_spec n 0).
            rewrite Nat2Z.inj_add in XX.
            rewrite Z2Nat.id in XX; try lia.
            rewrite zof in XX. lia. }
        destruct (Z_of_to_label_s G y Vy) as [ly [Hly [Hpos Hlab]]].
        destruct (Z_of_to_label_s G _ Vx) as [lx [Hlx [poskx Hlab']]].
        destruct (lsp G x (s G)) eqn:xs.
        + destruct (lsp G x y) as [K|] eqn:xy. simpl.
          2:{ simpl.
            generalize (lsp_codistance G x (s G) y).
            now rewrite xs Hly xy /=. }
          unshelve epose proof (Subgraph1.correct_labelling_lsp_G' _ _ _ _ _ _ xy) as XX;
            tas; try apply HI.
          set (G' := Subgraph1.G' G y x K) in XX.
          assert (HI' : invariants G'). { eapply Subgraph1.HI'; tas. }
          specialize (Hle _ XX); clear XX; cbn in Hle.
          assert (HG' : acyclic_no_loop G'). { apply Subgraph1.HG'; eauto. }
          assert (XX: (Some (- K) <= lsp G' y x)%nbar). {
            apply Subgraph1.lsp_G'_yx. apply Vy. }
          apply le_Some_lsp in XX as [yx [lspyx lekyx]].
          destruct (Z_of_to_label_s G' _ Vx) as [kx' [Hkx' [kx'pos zofx']]].
          cbn in *; rewrite zofx' in Hle.
          destruct (Z_of_to_label_s G' _ Vy) as [ky' [Hky' [ky'pos zofy']]].
          cbn in Hky'; rewrite zofy' in Hle; cbn in *.
          epose proof (Subgraph1.lsp_G'_spec_left G _ _ Vx Vy _ xy x).
          rewrite lspyx in H. rewrite lsp_xx in H. simpl in H.
          pose proof (lsp_sym _ xy).
          assert (yx = - K).
          { destruct (lsp G y x); simpl in *; injection H. simpl. lia. lia. }
          subst yx.
          pose proof (lsp_codistance G' (s G) y x).
          rewrite Hky' lspyx Hkx' in H1. simpl in H1. lia.

        + pose (K := if n <=? 0 then Z.max lx (Z.succ ly - n) else Z.max lx (Z.succ ly)).
          unshelve epose proof (correct_labelling_lsp_G' _ _ _ _ xs K) as XX;
            tas; try apply HI.
          set (G' := G' (s G) x K) in XX.
          assert (HI' : invariants G'). {
            eapply HI'; tas. apply HI. }
          specialize (Hle _ XX); clear XX; cbn in Hle.
          assert (XX: (Some K <= lsp G' (s G) x)%nbar). {
            apply lsp_G'_yx. apply HI. }
          assert (HG' : acyclic_no_loop G'). { apply HG'; eauto. apply HI. }
          destruct (Z_of_to_label_s G' _ Vx) as [kx' [Hkx' [kx'pos zofx']]].
          cbn in Hkx'; rewrite Hkx' in XX; cbn in *.
          rewrite zofx' in Hle.
          destruct (Z_of_to_label_s G' _ Vy) as [ky' [Hky' [ky'pos zofy']]].
          cbn in Hky'; rewrite zofy' in Hle; cbn in *.
          assert (Hle'' : K + n <= ky') by lia; clear Hle.
          enough ((Some ky' <= Some K + lsp G x y)%nbar) as HH. {
            revert HH. destruct (lsp G x y); cbn; auto. lia. }
          unshelve erewrite (lsp_G'_spec_left (s G) x _ xs K) in Hky'. apply HI.
          apply eq_max in Hky'. destruct Hky' as [Hk|Hk].
          -- rewrite Hly in Hk. apply some_inj in Hk.
            exfalso.
            clear -XX ky'pos Hk Hle''. subst. subst K.
            destruct (Z.leb_spec n 0); lia.
          -- rewrite Hk. reflexivity.
      - case_eq (lsp G x y).
        * intros m Hm l Hl. rewrite Hm in Hle.
          apply (lsp0_spec_eq G) in Hm. destruct Hm as [p Hp].
          pose proof (correct_labelling_PathOf G l Hl _ _ (to_pathOf G p)) as XX.
          rewrite <- sweight_weight, Hp in XX. cbn in Hle; lia.
        * intro X; rewrite X in Hle; inversion Hle.
    Defined.

    Lemma lsp_vset_in {s x y n} :
      lsp0 G s x y = Some n ->
      (n = 0 /\ x = y) \/ (VSet.In y (V G)).
    Proof using HI.
      intros H.
      eapply lsp0_spec_eq in H.
      destruct H. subst n. induction x0.
      simpl. left; auto. destruct IHx0 as [[sw ->]|IH].
      destruct e. simpl. specialize (edges_vertices _ _ i) as [Hs Ht]. right; apply Ht.
      right; auto.
    Qed.

    Lemma leq_vertices_caract {n x y} :
      leq_vertices G n x y <-> (if VSet.mem y (V G) then Some n <= lsp G x y
                             else (n <= 0)%Z /\ (x = y \/ Some n <= lsp G x (s G)))%nbar.
    Proof.
      case_eq (VSet.mem y (V G)); intro Vy;
        [apply VSet.mem_spec in Vy; now apply leq_vertices_caract0|].
      split.
      - intro Hle. apply VSetFact.not_mem_iff in Vy.
        assert (nneg : n <= 0).
        { pose (K := to_label (lsp G (s G) x)).
          pose (l := fun z => if V.eq_dec z y then K
                           else to_label (lsp G (s G) z)).
            unshelve refine (let XX := Hle l _ in _); subst l K.
            -- split.
              ++ destruct (V.eq_dec (s G) y).
                 apply False_rect. apply Vy. subst; apply HI.
                 now apply lsp_correctness.
              ++ intros e H.
                 destruct (V.eq_dec e..s y).
                 apply False_rect, Vy; subst; now apply HI.
                 destruct (V.eq_dec e..t y).
                 apply False_rect, Vy; subst; now apply HI.
                 now apply lsp_correctness.
            -- clearbody XX; cbn in XX.
               destruct (V.eq_dec y y) as [?|?]; simpl in *; [|contradiction].
               destruct (V.eq_dec x y) as [Hy|Hy]; simpl in *; [intuition|lia]. }
        split; auto.
        + destruct (V.eq_dec x y); [now left|right].
          case_eq (lsp G x (s G)); [intros; cbn; try lia|].
          ++ destruct (VSet.mem x (V G)) eqn:mem.
             2:{ enough (z = 0); try lia.
                 epose proof (lsp0_spec_eq G _ H) as [p wp].
                 assert (~ VSet.In x (V G)).
                 { intros inx. eapply VSet.mem_spec in inx. congruence. }
                 clear - HI HG H0 p wp.
                 depind p. simpl in wp. lia.
                 epose proof (edges_vertices G). destruct e.
                 specialize (H _ i) as [H _]. cbn in H. contradiction. }
             apply VSet.mem_spec in mem. red in Hle.
             unshelve epose proof (Subgraph1.correct_labelling_lsp_G' G (s G) x mem _ _ H) as X.
             now apply source_vertex.
            set (G' := Subgraph1.G' G (s G) x z) in X.
            assert (HI' : invariants G'). {
              eapply Subgraph1.HI'; tas. apply HI. }
            assert (HG' : acyclic_no_loop G'). {
              eapply Subgraph1.HG'; tas. apply HI. }
            pose (l := fun v => if V.eq_dec v y then 0%nat
                            else to_label (lsp G' (s G) v)).
            assert (XX : correct_labelling G l). {
              subst l; split.
              -- destruct (V.eq_dec (s G) y).
                apply False_rect. apply Vy. subst; apply HI.
                unfold lsp; rewrite acyclic_lsp0_xx; try assumption. reflexivity.
              -- intros e H'.
                destruct (V.eq_dec e..s y).
                apply False_rect, Vy; subst; now apply HI.
                destruct (V.eq_dec e..t y).
                apply False_rect, Vy; subst; now apply HI.
                simpl.
                now apply X. }
            specialize (Hle _ XX); subst l; cbn in *.
            destruct (V.eq_dec y y); [|contradiction].
            simpl in Hle.
            destruct (V.eq_dec x y); [contradiction|].
            simpl in Hle.
            destruct (lsp_s G' x) as [lx [lspx wx]]; auto.
            rewrite lspx in Hle.
            rewrite Z_of_to_label_pos in Hle. lia.
            assert (lx = - z).
            { enough (lsp G' (s G') x = Some (- z)). congruence.
              rewrite (Subgraph1.lsp_G'_spec_left G _ _ _ _ _ H x). auto.
              apply source_vertex; eauto.
              rewrite lsp_xx /=.
              pose proof (lsp_s G x mem) as [lx' [lspx' w]].
              enough (lsp G (s G) x <= Some (-z))%nbar. rewrite lspx' /= in H0.
              rewrite lspx'. simpl. f_equal. lia.
              apply (lsp_sym _ H). }
            subst lx. lia.

          ++ intros Hxs. simpl.
          case_eq (VSet.mem x (V G)); intro Vx.
          * apply VSet.mem_spec in Vx.
            assert (x <> s G).
            { destruct (V.eq_dec x (s G)) => //. rewrite e in Hxs.
              epose proof (lsp0_spec_le G (spath_refl G (V G) (s G))).
              rewrite /lsp in Hxs. now rewrite Hxs in H. }
            pose (K := Z.succ (- n - n) ).
            unshelve epose proof (correct_labelling_lsp_G' _ _ _ _ Hxs K) as X;
              tas; try apply HI.
            set (G' := G' (s G) x K) in X.
            assert (HI' : invariants G'). {
              eapply HI'; tas. apply HI. }
            assert (HG' : acyclic_no_loop G'). {
              eapply HG'; tas. apply HI. }
            pose (l := fun z => if V.eq_dec z y then Z.to_nat (-n)
                             else to_label (lsp G' (s G) z)).
            assert (XX : correct_labelling G l). {
              subst l; split.
              -- destruct (V.eq_dec (s G) y).
                 apply False_rect. apply Vy. subst; apply HI.
                 unfold lsp; rewrite acyclic_lsp0_xx; try assumption. reflexivity.
              -- intros e H'.
                 destruct (V.eq_dec e..s y).
                 apply False_rect, Vy; subst; now apply HI.
                 destruct (V.eq_dec e..t y).
                 apply False_rect, Vy; subst; now apply HI.
                 now apply X. }
            specialize (Hle _ XX); subst l; cbn in *.
            destruct (V.eq_dec y y) as [?|?]; [|contradiction].
            destruct (V.eq_dec x y) as [Hy|Hy]. simpl in *. contradiction.
            simple refine (let YY := lsp0_spec_le G'
                                (spath_step G' _ (V G) (s G) x x ?[XX] (K; _)
                                             (spath_refl _ _ _)) in _).
            [XX]: apply DisjointAdd_remove1. apply HI.
            apply EdgeSet.add_spec. left; reflexivity.
            clearbody YY; simpl in YY.
            case_eq (lsp0 G' (V G) (s G) x);
              [|intro HH; rewrite HH in YY; inversion YY].
            intros kx Hkx.
            unfold lsp in Hle; cbn in *; rewrite Hkx in YY, Hle.
            rewrite Z_of_to_label in Hle. simpl in YY.
            destruct (Z.leb_spec 0 kx).
            rewrite Z2Nat.id in Hle; lia.
            subst K. lia.
          * apply VSetFact.not_mem_iff in Vx.
            pose (K := to_label (lsp G (s G) x)).
            pose (l := fun z => if V.eq_dec z y then 0%nat
                             else if V.eq_dec z x then (Z.to_nat (- n) + 1)%nat
                             else to_label (lsp G (s G) z)).
            unshelve refine (let XX := Hle l _ in _); subst l K.
            -- split.
               +++ destruct (V.eq_dec (s G) y).
                  apply False_rect. apply Vy. subst; apply HI.
                  destruct (V.eq_dec (s G) x).
                  apply False_rect. apply Vx. subst; apply HI.
                  now apply lsp_correctness.
               +++ intros e H.
                  destruct (V.eq_dec e..s y).
                  apply False_rect, Vy; subst; now apply HI.
                  destruct (V.eq_dec e..t y).
                  apply False_rect, Vy; subst; now apply HI.
                  destruct (V.eq_dec e..s x).
                  apply False_rect, Vx; subst; now apply HI.
                  destruct (V.eq_dec e..t x).
                  apply False_rect, Vx; subst; now apply HI.
                  now apply lsp_correctness.
            -- clearbody XX; cbn in XX.
               destruct (V.eq_dec y y) as [?|?]; [|contradiction].
               destruct (V.eq_dec x y) as [Hy|Hy]. simpl in *; contradiction.
               destruct (V.eq_dec x x) as [?|?]; simpl in *; [lia|contradiction].
      - intros [e [Hxy|Hxs]] l Hl; subst; [lia|].
        case_eq (lsp G x (s G)); [|intro H; rewrite H in Hxs; inversion Hxs].
        intros k Hk.
        rewrite Hk in Hxs. simpl in Hxs.
        destruct (lsp0_spec_eq _ _ Hk) as [p Hp].
        epose proof (correct_labelling_PathOf G l Hl _ _ (to_pathOf G p)).
        rewrite (proj1 Hl) in H.
        simpl in Hxs. rewrite <- sweight_weight, Hp in H.
        lia.
    Defined.

    Definition leqb_vertices z x y : bool :=
      if VSet.mem y (V G) then if is_left (Nbar.le_dec (Some z) (lsp_fast G x y)) then true else false
      else (Z.leb z 0 && (V.eq_dec x y || Nbar.le_dec (Some z) (lsp_fast G x (s G))))%bool.

    Lemma leqb_vertices_correct n x y
      : leq_vertices G n x y <-> leqb_vertices n x y.
    Proof using HG HI.
      etransitivity. apply leq_vertices_caract.
      rewrite /leqb_vertices !lsp_optim.
      destruct (VSet.mem y (V G)).
      - destruct (le_dec (Some n) (lsp G x y)); cbn; intuition.
        discriminate.
      - symmetry; etransitivity. apply andb_and.
        apply Morphisms_Prop.and_iff_morphism.
        apply Z.leb_le.
        etransitivity. apply orb_true_iff.
        apply Morphisms_Prop.or_iff_morphism.
        destruct (V.eq_dec x y); cbn; intuition; try discriminate.
        destruct (le_dec (Some n) (lsp G x (s G))); cbn; intuition.
        discriminate.
    Qed.

  End subgraph.

  Definition edge_map (f : Edge.t -> Edge.t) (es : EdgeSet.t) : EdgeSet.t :=
    EdgeSetProp.of_list (map f (EdgeSetProp.to_list es)).

  Lemma edge_map_spec1 f es : forall e, EdgeSet.In e es -> EdgeSet.In (f e) (edge_map f es).
  Proof.
    move=> e /EdgeSet.elements_spec1/InA_In_eq ?.
    apply/EdgeSetProp.of_list_1; apply/InA_In_eq.
    by apply: in_map.
  Qed.

  Lemma edge_map_spec2 f es e :
    EdgeSet.In e (edge_map f es) <-> exists e0, e = f e0 /\ EdgeSet.In e0 es.
  Proof.
    split.
    - move=> /EdgeSetProp.of_list_1/InA_In_eq/in_map_iff.
      move=> [x [<- /InA_In_eq/EdgeSet.elements_spec1 ?]].
      exists x; by split.
    - move=> [? [->]]; apply: edge_map_spec1.
  Qed.

  Definition diff (l : labelling) x y := Z.of_nat (l y) - Z.of_nat (l x).

  Definition relabel (G : t) (l : labelling) : t :=
    (V G, edge_map (fun e => (e..s , diff l e..s e..t, e..t)) (E G), s G).

  Lemma relabel_weight G l (Gl := relabel G l) :
    forall x y (p : PathOf Gl x y), weight p = Z.of_nat (l y) - Z.of_nat (l x).
  Proof.
    move=> x y; elim => [?/=|??? [? /= /edge_map_spec2 [?[[=]????]]] ? ->].
    2: subst; unfold diff.
    all: lia.
  Qed.

  Lemma relabel_lsp G l (Gl := relabel G l) :
    forall x y n, lsp Gl x y = Some n -> n = Z.of_nat (l y) - Z.of_nat (l x).
  Proof.
    move=> ??? /lsp0_spec_eq [p <-].
    rewrite sweight_weight. apply: relabel_weight.
  Qed.

  Lemma acyclic_relabel G l (Gl := relabel G l) :
    correct_labelling G l ->
    acyclic_no_loop Gl.
  Proof.
    move=> HGl x p; rewrite relabel_weight.
    have acG := acyclic_labelling G l HGl.
    have xx0 := @lsp_xx G acG x.
    move: (correct_labelling_lsp G xx0 l HGl); lia.
  Qed.

  Definition relabel_path G l (Gl := relabel G l) :
    forall {x y}, PathOf G x y -> PathOf Gl x y.
  Proof.
    move=> x y; elim=> {x y}[x| x y z e p ih]; first constructor.
    pose n := Z.of_nat (l y) - Z.of_nat (l x).
    econstructor; last exact ih.
    eexists; apply: (edge_map_spec1 _ _ _ e.π2).
  Defined.

  Lemma invariants_relabel G l (Gl := relabel G l) :
    correct_labelling G l ->
    invariants G ->
    invariants Gl.
  Proof.
    move=> [sG0 _] [edgeG sG wG] ; constructor.
    - move=> e /edge_map_spec2 [e' [-> ?]]; cbn; by apply: edgeG.
    - apply: sG.
    - move=> x xin; move: (wG x xin)=> [[p h]].
      constructor.
      exists (relabel_path G l p).
      constructor; rewrite relabel_weight sG0; lia.
  Qed.

  Definition relabel_map G1 l (e : Edge.t) : Edge.t :=
    if EdgeSet.mem e (E G1)
    then (e..s , diff l e..s e..t, e..t)
    else e.

  Definition relabel_on (G1 G2 : t) (l : labelling) : t :=
    (V G2, edge_map (relabel_map G1 l) (E G2), s G2).

  Lemma weight_inverse G x y (p : PathOf G x y) (q : PathOf G y x) :
    acyclic_no_loop G ->
    weight p <= - weight q.
  Proof.
    move=> /(_ x (concat _ p q)); rewrite weight_concat; lia.
  Qed.

  Lemma sweight_inverse {G x y s s'} (p : SPath G s x y) (q : SPath G s' y x) :
    acyclic_no_loop G ->
    sweight p <= - sweight q.
  Proof.
    move=> acG.
    move: (weight_inverse G x y (to_pathOf _ p) (to_pathOf _ q) acG).
    by rewrite !sweight_weight.
  Qed.


  Definition acyclic_no_sloop G :=
    forall x s (p : SPath G s x x), sweight p > 0 -> False.

  Lemma acyclic_no_loop_sloop G (invG : invariants G) :
    acyclic_no_loop G <-> acyclic_no_sloop G.
  Proof.
    etransitivity; first apply: acyclic_no_loop_loop'.
    split.
    - move=> acG x s p wp. apply: (acG x).
      exists (to_pathOf _ p).
      by rewrite -sweight_weight.
    - move=> acG x [p wp].
      pose (rx := spath_refl G VSet.empty x).
      have hsupp : VSet.Equal (VSet.union VSet.empty (nodes G p)) (nodes G p).
      { apply: VSetProp.empty_union_1. apply: VSet.empty_spec. }
      unshelve epose (simplify G p rx hsupp).
      apply: (acG s0.π1 _ s0.π2).
      move: (weight_simplify G p rx hsupp).
      rewrite {1}/rx /s0 /=; lia.
  Qed.

  Lemma DisjointAdd_add4 x s1 s2 : DisjointAdd x s1 s2 -> DisjointAdd x s1 (VSet.add x s2).
  Proof.
    move=> [addx xnotins1]. split=> // y.
    etransitivity. apply VSet.add_spec. split.
    - move=> [?|/addx //]; by left.
    - move=> /addx; by right.
  Qed.

  Lemma DisjointAdd_In {x s1 s2} : DisjointAdd x s1 s2 -> VSet.In x s2.
  Proof. move=> [h _]; apply/h; by left. Qed.


  Lemma reroot_spath_aux1 {x s0 s1 s2} :
    DisjointAdd x s1 s2 -> Disjoint s2 s0 ->
    VSet.Subset (VSet.union s1 (VSet.add x s0)) (VSet.union s2 s0).
  Proof.
    move=> disjadd dijs20 ? /VSet.union_spec [].
    1:move=> /(DisjointAdd_Subset disjadd) ?; apply/VSet.union_spec; by left.
    move=> /VSet.add_spec[->|?]; apply/VSet.union_spec; [left| by right].
    apply: DisjointAdd_In; eassumption.
  Qed.

  Lemma reroot_spath_aux2 {x s0 s1 s2} :
    DisjointAdd x s1 s2 -> Disjoint s2 s0 ->
    DisjointAdd x s0 (VSet.add x s0).
  Proof.
    move=> disjadd disj20; apply: DisjointAdd_add2.
    have ?:= DisjointAdd_In disjadd.
    move=> xins'; apply: (disj20 x); apply/VSet.inter_spec; by split.
  Qed.

  Lemma reroot_spath_aux3 {x s0 s1 s2} :
    DisjointAdd x s1 s2 -> Disjoint s2 s0 ->
    Disjoint s1 (VSet.add x s0).
  Proof.
    move=> disjadd disj20.
    have disj0' : Disjoint s1 s0 by
      (apply: Disjoint_DisjointAdd; eassumption).
    move=> ? /VSet.inter_spec [ins0] /VSet.add_spec [].
    1: move=> eq; rewrite eq in ins0; case: disjadd=> _ /(_ ins0)//.
    move=> ?; apply: disj0'; apply/VSet.inter_spec; split; eassumption.
  Qed.

  Definition reroot_spath_aux G s x z (p : SPath G s x z) y :
    VSet.In y (snodes G p) ->
    forall s' (q : SPath G s' z x),
      Disjoint s s' -> exists c : SPath G (VSet.union s s') y y,
                        sweight c = sweight p + sweight q .
  Proof.
    elim: p=> {x z}[s0 x|s0 s1 x y' z disj01 e p ih] /=.
    - move=> /VSetFact.empty_iff [].
    - case: (VSet.E.eq_dec y x)=> [->| neq].
      * move=> _ s' q disj'; unshelve econstructor.
        + refine (sconcat G (spath_step G s0 s1 _ _ _ disj01 e p) disj' q).
        + rewrite sweight_sconcat //=.
      * move=> /VSetDecide.MSetDecideTestCases.test_add_In /(_ neq).
        move=> yinp s' q disj'.
        move: (ih yinp (VSet.add x s')
                  (add_end G q e (reroot_spath_aux2 disj01 disj'))
                  (reroot_spath_aux3 disj01 disj'))=> [ihc ihw].
        unshelve eexists (SPath_sub _ _ ihc).
        1: apply: reroot_spath_aux1=> //.
        rewrite weight_SPath_sub ihw /= weight_add_end;lia.
  Qed.

  Lemma reroot_spath G s x (p : SPath G s x x) y :
    VSet.In y (snodes G p) ->
    exists c : SPath G s y y, sweight c = sweight p.
  Proof.
    move=> yinp.
    pose (rx := spath_refl G VSet.empty x).
    have disj : Disjoint s VSet.empty
      by move=> ? /VSet.inter_spec [_] /VSet.empty_spec [].
    case: (reroot_spath_aux G s x x p y yinp _ rx disj)=> c wc.
    unshelve eexists.
    + apply: (SPath_sub _ _ c).
      move=> ? /VSet.union_spec [//|/VSet.empty_spec[]].
    + rewrite weight_SPath_sub wc /rx /=; lia.
  Qed.

  Section MapSPath.
    Context {G1 G2} (on_edge : forall x y, EdgeOf G1 x y -> EdgeOf G2 x y).

    Equations map_path {x y} (p : PathOf G1 x y) : PathOf G2 x y :=
    | pathOf_refl _ x => pathOf_refl _ x
    | pathOf_step _ x y' z e p =>
        pathOf_step _ x y' z (on_edge _ _ e) (map_path p).

    Definition weight_map_path1
               (weight_on_edge : forall x y e, (on_edge x y e).π1 <= e.π1) :
      forall x y (p : PathOf G1 x y),
        weight (map_path p) <= weight p.
    Proof using Type.
      move=> x y p; apply_funelim (map_path p); simp map_path; cbn=> //.
      move=> ??? e ?; move: (weight_on_edge _ _ e); lia.
    Qed.

    Definition weight_map_path2
              (weight_on_edge : forall x y e, (on_edge x y e).π1 >= e.π1) :
      forall x y (p : PathOf G1 x y),
        weight (map_path p) >= weight p.
    Proof using Type.
      move=> x y p; apply_funelim (map_path p); simp map_path; cbn=> //.
      move=> ??? e ?; move: (weight_on_edge _ _ e); lia.
    Qed.


    Equations map_spath {s x y} (p : SPath G1 s x y) : SPath G2 s x y :=
    | spath_refl _ s x => spath_refl _ s x
    | spath_step _ s1 s2 x y' z d e p =>
        spath_step _ s1 s2 x y' z d (on_edge _ _ e) (map_spath p).


    Definition weight_map_spath1
              (weight_on_edge : forall x y e, (on_edge x y e).π1 <= e.π1) :
      forall s x y (p : SPath G1 s x y),
        sweight (map_spath p) <= sweight p.
    Proof using Type.
      move=> s x y p; apply_funelim (map_spath p); simp map_spath; cbn=> //.
      move=> ?????? e ?; move: (weight_on_edge _ _ e); lia.
    Qed.

    Definition weight_map_spath2
              (weight_on_edge : forall x y e, (on_edge x y e).π1 >= e.π1) :
      forall s x y (p : SPath G1 s x y),
        sweight (map_spath p) >= sweight p.
    Proof using Type.
      move=> s x y p; apply_funelim (map_spath p); simp map_spath; cbn=> //.
      move=> ?????? e ?; move: (weight_on_edge _ _ e); lia.
    Qed.

    Definition lsp_map_path2
               (vsub : VSet.Subset (V G1) (V G2))
               (weight_on_edge : forall x y e, (on_edge x y e).π1 >= e.π1) :
      forall x y, (lsp G1 x y <= lsp G2 x y)%nbar.
    Proof using Type.
      move=> x y; case E1 : (lsp G1 x y)=> //.
      move: E1=> /lsp0_spec_eq [p wp].
      etransitivity.
      2:{ apply: lsp0_spec_le.
          apply: SPath_sub; last exact (map_spath p); assumption.
      }
      apply: Z.ge_le.
      rewrite -wp weight_SPath_sub.
      by apply: weight_map_spath2.
    Qed.

  End MapSPath.

  Lemma lsp_edge G `{invariants G} {x y} (e : EdgeOf G x y) : (Some e.π1 <= lsp G x y)%nbar.
  Proof.
    have xin : VSet.In x (V G) by case: (edges_vertices G _ e.π2).
    pose proof (l := lsp0_spec_le G (spath_one G xin e.π2)).
    cbn in l. rewrite Z.add_0_r in l. assumption.
  Qed.


  Section FirstVertexIn.
    Context (G1 G2 : t).

    Equations first_in {s x y} (p : SPath G2 s x y) : V.t :=
    | spath_refl _ z => z
    | spath_step s1 s2 x0 y0 z0 d e q with VSet.mem x0 (V G1) => {
      | true => x0
      | false => first_in q
      }.

    Lemma first_in_in {s x y} (p : SPath G2 s x y) :
      VSet.In y (V G1) -> VSet.In (first_in p) (V G1).
    Proof using Type.
      apply_funelim (first_in p); simp first_in.
      move=> ???????? /VSet.mem_spec //.
    Qed.

    Lemma first_in_first {s x y} (p : SPath G2 s x y) :
      VSet.In x (V G1) -> first_in p = x.
    Proof using Type.
      apply_funelim (first_in p); simp first_in=> //.
      move=> ????????? /VSetDecide.F.not_mem_iff //.
    Qed.

  End FirstVertexIn.

  Section RelabelOn.
    Context G1 G2 l (Gl := relabel_on G1 G2 l).
    Context `{invariants G1}.

    Context (preserves_edges: forall e, EdgeSet.In e (E G1) -> EdgeSet.In e (E G2)).

    Definition from1 [x y] : EdgeOf G1 x y -> EdgeOf Gl x y.
    Proof.
      move=> e. exists (diff l x y).
      replace (_,_,_) with (relabel_map G1 l (x, e.π1, y)) by
        (unfold relabel_map; move: e.π2=> /EdgeSet.mem_spec -> //=).
      unfold Gl, relabel_on; cbn.
      apply: edge_map_spec1; apply: preserves_edges; apply: e.π2.
    Defined.

    Definition from2 [x y] : EdgeOf G2 x y -> EdgeOf Gl x y.
    Proof.
      move=> e.
      exists (if (EdgeSet.mem (x, e.π1, y) (E G1)) then diff l x y else e.π1).
      case E: (EdgeSet.mem (x, e.π1, y) (E G1)).
      + apply EdgeSet.mem_spec in E.
        exact (from1 (e.π1 ; E)).π2.
      + replace (_,_,_) with (relabel_map G1 l (x, e.π1, y))
          by rewrite /relabel_map E //.
      unfold Gl, relabel_on; cbn.
      apply: edge_map_spec1; apply: e.π2.
    Defined.


    Context (HGl : correct_labelling G1 l)
            `{invariants G2}.


    Context `{acyclic_no_loop G2}
            (embed : forall v1 v2, VSet.In v1 (V G1) -> VSet.In v2 (V G1) ->
                              (lsp G2 v1 v2 <= lsp G1 v1 v2)%nbar).
    Lemma relabel_on_lsp_G1 {x y w} :
      (Some w <= lsp G1 x y)%nbar -> w <= diff l x y.
    Proof using HGl.
      case Elsp: (lsp _ _ _)=> [n /=|]; last move=> [].
      pose proof (h := correct_labelling_lsp G1 Elsp l HGl).
      move: h; unfold diff; lia.
    Qed.

    Lemma relabel_on_lsp_G2 {x y w} :
      VSet.In x (V G1) ->
      VSet.In y (V G1) ->
      (Some w <= lsp G2 x y)%nbar -> w <= diff l x y.
    Proof using HGl embed.
      move=> hx hy le1.
      move: (le_trans _ _ _ le1 (embed _ _ hx hy)).
      apply: relabel_on_lsp_G1.
    Qed.


    Lemma weight_from1 [x y] (e : EdgeOf G1 x y) : (from1 e).π1 >= e.π1.
    Proof using H HGl.
      apply: Z.le_ge.
      apply: relabel_on_lsp_G1.
      apply: lsp_edge.
    Qed.

    Lemma weight_from2 [x y] (e : EdgeOf G2 x y) : (from2 e).π1 >= e.π1.
    Proof using H HGl.
      cbn; case E: (EdgeSet.mem _ _); last lia.
      apply EdgeSet.mem_spec in E.
      exact (weight_from1 (e.π1 ; E)).
    Qed.

    Lemma relabel_on_invariants : invariants Gl.
    Proof using H H0 HGl preserves_edges.
      constructor.
      - move=> e /edge_map_spec2 [e0 [->]] /(edges_vertices G2)[??].
        unfold relabel_map; case: (EdgeSet.mem _ _)=> //.
      - apply: (source_vertex G2).
      - move=> x /(source_pathOf G2 x) [[p [wp]]].
        constructor.
        exists (map_path from2 p).
        constructor. etransitivity; first eassumption.
        apply: Z.ge_le.
        apply: weight_map_path2.
        apply: weight_from2.
    Qed.


    Lemma sweight_relabel_on_G1 {s x y} (p : SPath Gl s x y) :
      VSet.In y (V G1) ->
      exists n, lsp G2 x (first_in G1 Gl p) = Some n /\
             sweight p <= n + diff l (first_in G1 Gl p) y.
    Proof using H H0 H1 HGl embed.
      move=> yin.
      induction p.
      2:move: e => [w /= h];
        move: {-}(h) => /edge_map_spec2 [e0 [+ e0G2]];
        unfold relabel_map; case E: (EdgeSet.mem _ _).
      - simp first_in.
        exists 0; split; first rewrite lsp_xx //.
        rewrite /diff /=; lia.
      - move=> [=] ???; subst.
        apply EdgeSet.mem_spec in E.
        destruct e0 as [[x0 ?]?].
        simp first_in. cbn.
        case: (edges_vertices G1 _ E)=> [] /VSet.mem_spec -> ? /=.
        exists 0; split; first rewrite lsp_xx //.
        move: (IHp yin)=> [? []].
        rewrite first_in_first //=.
        rewrite lsp_xx /diff=> [=] <-.
        lia.
      - simp first_in.
        pose proof (lc := lsp_codistance G2 x y (first_in G1 Gl p)).
        destruct e0 as [[s w0] t].
        pose proof (lbw := lsp_edge G2 (w0 ; e0G2)).
        move: (IHp yin) lc=> [w1 []] -> /= wpb + [=] ???; subst.
        move: {lbw}(plus_le_compat _ _ _ _ lbw (le_refl (Some w1)))=> /= le1 le2.
        move: {le1 le2}(le_trans _ _ _ le1 le2)=> le.
        case Ex: (VSet.mem s _)=> /=.
        + exists 0; split; first rewrite lsp_xx //.
          move: Ex=> /VSet.mem_spec=> sin.
          move: (relabel_on_lsp_G2 (sin) (first_in_in G1 Gl p yin) le)=> /=.
          move: wpb; unfold diff. lia.
        + move: le; case E2: (lsp _ _ _)=> [n /=|]; last move=> [].
          move=> le; exists n; split=> //.
          move: wpb le; unfold diff; lia.
    Qed.

    Lemma sweight_relabel_on_G2 {s x y} (p : SPath Gl s x y) :
      Disjoint (snodes Gl p) (V G1) ->
      (Some (sweight p) <= lsp G2 x y)%nbar.
    Proof using H H0 H1 l.
      induction p=> /=; first rewrite lsp_xx //.
      move=> disj.
      apply: le_trans; last apply: (lsp_codistance G2 x y z).
      change (Some (?x + ?y)) with (Some x + Some y)%nbar.
      apply: plus_le_compat; last apply: IHp.
      + move: e=> [w]. unfold Gl, relabel_on; cbn.
        move=> /edge_map_spec2 [[[s w'] t]].
        unfold relabel_map.
        case E0: (EdgeSet.mem _ _).
        * move: E0=> /EdgeSet.mem_spec /(edges_vertices G1 _) [sin ?] [] [=] ???.
          subst; exfalso; apply: (disj s).
          apply/VSet.inter_spec; split=> //; by apply: VSetFact.add_1.
        * move=> [] [=] ??? e2; subst.
          exact (lsp_edge G2 (w' ; e2)).
      + move=> v /VSet.inter_spec [??]; apply: (disj v).
        apply/VSet.inter_spec; split=> //.
        by apply: VSetFact.add_2.
    Qed.

  Lemma acyclic_relabel_on : acyclic_no_sloop Gl.
  Proof using H H0 H1 HGl embed.
    move=> x s p wp.
    case E: (VSet.choose (VSet.inter (snodes Gl p) (V G1))) => [y|].
    - move: E=> /VSet.choose_spec1/VSet.inter_spec [yinp yin1].
      move: (reroot_spath Gl _ _ p y yinp)=> [q wq].
      move: (sweight_relabel_on_G1 q yin1)=> [? []].
      rewrite first_in_first // lsp_xx=> [=] <-.
      rewrite wq. move: wp; unfold diff. lia.
    - move: E wp=> /VSet.choose_spec2 /(sweight_relabel_on_G2 p).
      rewrite lsp_xx /=; lia.
  Qed.


  Derive Subterm for SPath.
  Next Obligation.
    apply: Transitive_Closure.wf_clos_trans.
    move=> [[s0 [x0 y0/=]] p0].
    induction p0.
    - constructor=> -[[s1 [x1 y1/=]] p1] h. inversion h.
    - constructor=> -[[s1 [x1 y1/=]] p1] h.
      depelim h.
      move: IHp0.
      set sig0 := sigmaI _ _ _.
      set sig1 := sigmaI _ _ _.
      have -> // : sig0 = sig1.
      rewrite {}/sig0 {}/sig1.
      apply (f_equal (SPath_sig_pack _ s' x z)) in H4.
      noconf H4.
      pose (f := fun p : (@sigma VSet.t
                               (fun s' : VSet.t =>
                                  @sigma V.t
                                         (fun x : V.t =>
                                            @sigma V.t
                                                   (fun y : V.t =>
                                                      @sigma V.t
                                                             (fun z : V.t =>
                                                                @sigma (DisjointAdd x s0 s')
                                                                       (fun d : DisjointAdd x s0 s' =>
                                                                          @sigma (EdgeOf G x y)
                                                                                 (fun e : EdgeOf G x y => SPath G s0 y z))))))) =>
                   sigmaI (fun x => SPath G (pr1 x) (pr1 (pr2 x)) (pr2 (pr2 x)))
                          {| pr1 := s0 ;
                            pr2 := sigmaI (fun _ : V.t => V.t)
                                          (pr1 (pr2 (pr2 p)))
                                          (pr1 (pr2 (pr2 (pr2 p)))) |}
                          (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 p))))))).
      apply: (f_equal f H4).
  Qed.

    Lemma spathG1_lsp_Gl x y :
      VSet.Subset (V G1) (V G2) ->
      SPath G1 (V G1) x y -> (Some (diff l x y) <= lsp Gl x y)%nbar.
    Proof using preserves_edges.
      move=> vsub p.
      pose q := SPath_sub Gl vsub (map_spath from1 p).
      replace (diff _ _ _) with (sweight q).
      1: apply: lsp0_spec_le.
      move: (V G1) p (V G2) vsub @q=> V0 p; induction p=> s1 vsub.
      - simp map_spath; cbn; first (unfold diff; lia).
      - simp map_spath. simpl.
        set vsub' := (fun _ => _). clearbody vsub'.
        move: (IHp _ vsub') => /= ->; unfold diff; lia.
    Qed.

    Lemma lsp_Gl_upperbound_G1  x y :
      VSet.In x (V G1) -> VSet.In y (V G1) ->
      forall n, lsp Gl x y = Some n -> n <= diff l x y.
    Proof using H H0 H1 HGl embed.
      move=> xin yin n /lsp0_spec_eq [p <-].
      pose proof (bound := sweight_relabel_on_G1 p yin).
      move: bound; rewrite first_in_first // lsp_xx => -[?] [[=]] <- //.
    Qed.

    Lemma lsp_Gl_between_G1 x y :
      VSet.Subset (V G1) (V G2) ->
      PathOf G1 x y ->
      VSet.In x (V G1) ->
      VSet.In y (V G1) ->
      lsp Gl x y = Some (diff l x y).
    Proof using H H0 H1 HGl embed preserves_edges.
      move=> vsub p xin yin.
      pose proof (q := simplify2' G1 p).
      pose proof (lb := spathG1_lsp_Gl _ _ vsub q).
      move: lb; case Elsp: (lsp _ _ _)=> [w|]; last move=> [].
      pose proof (ub := lsp_Gl_upperbound_G1 _ _ xin yin _ Elsp).
      move=> /= ?; f_equal; lia.
    Qed.

  End RelabelOn.

  Record subgraph (G1 G2 : t) : Prop := {
      vertices_sub : VSet.Subset (V G1) (V G2) ;
      edges_sub : EdgeSet.Subset (E G1) (E G2) ;
      same_src : s G1 = s G2
    }.

  Definition subgraph_on_edge {G1 G2} :
    subgraph G1 G2 ->
    forall x y, EdgeOf G1 x y -> EdgeOf G2 x y.
  Proof.
    move=> embed x y [w ine]; exists w.
    exact (edges_sub _ _ embed _ ine).
  Defined.

  Lemma subgraph_acyclic G1 G2 :
    subgraph G1 G2 -> acyclic_no_loop G2 -> acyclic_no_loop G1.
  Proof.
    move=> sub acG2 x p.
    etransitivity.
    2: apply: acG2; refine (map_path (subgraph_on_edge sub) p).
    apply: Z.ge_le; apply: weight_map_path2=> ?? [??] /=; lia.
  Qed.


  Record full_subgraph (G1 G2 : t) : Prop := {
      is_subgraph :> subgraph G1 G2 ;
      lsp_dominate :
      forall v1 v2, VSet.In v1 (V G1) -> VSet.In v2 (V G1) ->
               (lsp G2 v1 v2 <= lsp G1 v1 v2)%nbar
    }.

  Local Obligation Tactic := idtac.
  Local Unset Program Cases.
  #[program, local]
  Instance reflectEq_vertices : ReflectEq (VSet.E.t) :=
    Build_ReflectEq (VSet.E.t)
                    (fun x y => if VSet.E.compare x y is Eq then true else false)
                    _.
  Next Obligation.
    move=> x y. move: (VSet.E.compare_spec x y) => [->||].
    1: by apply: reflectP.
    all: move=> p; apply: reflectF=> eq; move: p; rewrite eq.
    all: have := (@irreflexivity _ _ (@StrictOrder_Irreflexive _ _ VSet.E.lt_strorder) y)=> //.
  Qed.

  #[program, local]
  Instance reflectEq_Z : ReflectEq Z :=
    Build_ReflectEq Z Z.eqb _.
  Next Obligation.
   intros; apply reflect_reflectProp; apply Z.eqb_spec.
  Qed.

  #[local]
  Instance reflectEq_nbar: ReflectEq Nbar.t :=
    @reflect_option Z reflectEq_Z.


  Module IsFullSubgraph.
    Section Border.
      Context (G1 : t) (ext : EdgeSet.t).
      Definition add_from_orig v s :=
        if VSet.mem v (V G1) then VSet.add v s else s.
      Definition fold_fun e s := add_from_orig (e..s) (add_from_orig (e..t) s).

      Definition border_set : VSet.t :=
        EdgeSet.fold fold_fun ext VSet.empty.

      Lemma EdgeSet_fold_spec_right2 (s : EdgeSet.t)
            (i : VSet.t) (f : EdgeSet.elt -> VSet.t -> VSet.t) :
        transpose VSet.Equal f ->
        Proper (eq ==> VSet.Equal ==> VSet.Equal) f ->
        VSet.Equal (EdgeSet.fold f s i) (fold_right f i (EdgeSet.elements s)).
      Proof using Type.
        move=> trf prpf; rewrite EdgeSet.fold_spec.
        elim: {s}(EdgeSet.elements s)=> // x l /= <-.
        elim: l i=> //= a l ih i.
        enough (forall l, Proper (VSet.Equal ==> VSet.Equal) (fold_left (fun a e => f e a) l)).
        1: by rewrite -ih trf.
        clear -prpf; elim=> //= ?? ih ?? -> //.
      Qed.

      Lemma add_from_orig_spec x v s :
        VSet.In x (add_from_orig v s) <-> (x = v /\ VSet.In x (V G1)) \/ VSet.In x s.
      Proof using Type.
        unfold add_from_orig.
        move E: (VSet.mem _ _)=> [].
        - move: E=> /VSet.mem_spec ?; rewrite VSet.add_spec; intuition.
          rewrite H0; left; intuition.
        - intuition; subst; exfalso.
          move: E=> /VSetFact.not_mem_iff; by apply.
      Qed.

      Lemma fold_fun_spec x e s :
        VSet.In x (fold_fun e s) <->
          ((x = e..s \/ x = e..t) /\ VSet.In x (V G1)) \/ VSet.In x s.
      Proof using Type.
        unfold fold_fun.
        rewrite 2!add_from_orig_spec; split.
        - move=> [[??]|[[??]|?]]; intuition.
        - move=> [[[?|?] ?]| ?]; intuition.
      Qed.

      #[local]
      Instance: Proper (eq ==> VSet.Equal ==> VSet.Equal) fold_fun.
      Proof using Type.
        unfold fold_fun, add_from_orig.
        move=> ? [[??]?] -> ??; cbn; move: (VSet.mem _ _) (VSet.mem _ _)=> [] [] -> //.
      Qed.

      Lemma border_set_spec x :
        VSet.In x border_set <->
          exists e, EdgeSet.In e ext /\ (x = e..s \/ x = e..t) /\ VSet.In x (V G1).
      Proof using Type.
        have <- :
          (exists e, In e (EdgeSet.elements ext) /\ (x = e..s \/ x = e..t) /\ VSet.In x (V G1))
          <->
          (exists e, EdgeSet.In e ext /\ (x = e..s \/ x = e..t) /\ VSet.In x (V G1))
          by
          (split; move=> [e [? ?]]; exists e; split=> //;
             by [apply/EdgeSet.elements_spec1/InA_In_eq|
                  apply/InA_In_eq/EdgeSet.elements_spec1]).
        rewrite /border_set EdgeSet_fold_spec_right2.
        1:{ move=> [[xs ?] xt] [[ys ?] yt] ?; cbn.
            unfold fold_fun, add_from_orig.
            move: (VSet.mem xs _) (VSet.mem xt _) (VSet.mem ys _) (VSet.mem yt _)=> [] [] [] []; try sets.
        }
        elim: (EdgeSet.elements _)=> [| e es ih] /=.
        - split.
          1: move=> /VSet.empty_spec [].
          move=> [? [[]]].
        - rewrite fold_fun_spec; split.
          + move=> [?|]; first (exists e; intuition).
            move=> /ih [e0 [? ?]]; exists e0; split=>//; by right.
          + move=> [e0 [[->|?] ?]]; first by left.
            right. apply/ ih; exists e0; split=> //.
      Qed.
    End Border.

    Section LspBoundExtendBorder.
      Context (G1 G2 : t) `{invariants G1} (ext := EdgeSet.diff (E G2) (E G1)).
      Let bs := (border_set G1 ext).

      Lemma spath_on_border s x y z
            (eo : EdgeOf G2 x y) (p : SPath G2 s y z) :
        VSet.In x (V G1) -> VSet.In z (V G1) ->
        ~(EdgeSet.In (x, eo.π1, y) (E G1)) ->
        VSet.In x bs /\ VSet.In (first_in G1 G2 p) bs.
      Proof using H.
        set (e := (_, _, _)).
        move=> hx hz heo.
        have he : EdgeSet.In e ext
          by (apply: EdgeSetFact.diff_3=> //; exact (eo.π2)).
        split.
        - apply/border_set_spec. exists e. repeat split=> //; last by left.
        - move: {hx}x {eo}(eo.π1) hz {heo}@e he; clear -p H.
          apply_funelim (first_in G1 G2 p)=> [????? e ?|???????? /VSet.mem_spec ???? e ?|].
          1,2: apply/border_set_spec; exists e; intuition.
          move=> ?????? e ? ih /VSetFact.not_mem_iff h ? ? ???.
          apply: ih=> //.
          apply: EdgeSetFact.diff_3; first exact (e.π2).
          move=> /edges_vertices [+ _] //.
      Qed.


      Lemma sweight_bound0
            `{invariants G2}
            `{acyclic_no_loop G1, acyclic_no_loop G2}
            (h : forall x y, VSet.In x bs -> VSet.In y bs -> (lsp G2 x y <= lsp G1 x y)%nbar)
            s x y (p : SPath G2 s x y) :
        VSet.In y (V G1) ->
        (Some (sweight p) <= lsp G2 x (first_in G1 G2 p) + lsp G1 (first_in G1 G2 p) y)%nbar.
      Proof using H.
        elim: {s x y}p.
        - move=> ??? /=; rewrite first_in_first // 2!lsp_xx //=.
        - move=> ?? x y z ? e q ih hz.
          simp first_in.
          case Ee : (EdgeSet.mem (x, e.π1, y) (E G1)).
          + apply EdgeSet.mem_spec in Ee.
            destruct (edges_vertices _ _ Ee) as [hx hy].
            move: (hx)=> /VSet.mem_spec -> /=; simp first_in.
            pose proof (lsp_codistance G1 x y z).
            move: (ih hz).
            rewrite first_in_first // 2!lsp_xx.
            pose proof (lsp_edge G1 (e.π1 ; Ee)).
            move: H3 H4.
            move: (lsp _ _ _) (lsp _ _ _) (lsp _ _ _)=> [?|] [?|] [?|]//=.
            lia.
          + apply EdgeSetFact.not_mem_iff in Ee.
            pose proof (lsp_edge G2 e).
            case Ex : (VSet.mem _ _); simp first_in.
            * cbn. rewrite lsp_xx add_0_l.
              specialize (ih hz).
              apply VSet.mem_spec in Ex.
              destruct (spath_on_border _ x y _ e q Ex hz Ee) as [hx' hf].
              etransitivity; last apply: (lsp_codistance G1 x (first_in G1 G2 q) z).
              etransitivity.
              1: rewrite add_finite; apply: plus_le_compat; eassumption.
              rewrite add_assoc. apply: plus_le_compat; last reflexivity.
              etransitivity; last apply: h=> //.
              apply: lsp_codistance.
            * cbn.
              etransitivity.
              2: apply: plus_le_compat; last reflexivity.
              2: apply: (lsp_codistance _ x y).
              rewrite add_finite -add_assoc; apply: plus_le_compat=> //.
              by apply: ih.
      Qed.

      Lemma lsp_bound_extend_border
            `{invariants G2}
            `{acyclic_no_loop G1, acyclic_no_loop G2}
            (h : forall x y, VSet.In x bs -> VSet.In y bs -> (lsp G2 x y <= lsp G1 x y)%nbar)
            x y : VSet.In x (V G1) -> VSet.In y (V G1) ->
                  (lsp G2 x y <= lsp G1 x y)%nbar.
      Proof using H.
        move=> hx hy.
        case E: (lsp G2 x y) => //.
        move: E=> /lsp0_spec_eq [p hp].
        pose proof (hb := sweight_bound0 h _ _ _ p hy).
        move: hb. rewrite hp first_in_first // lsp_xx add_0_l //.
      Qed.
    End LspBoundExtendBorder.

    Definition is_full_extension (G1 G2 : t) : bool :=
      let ext := EdgeSet.diff (E G2) (E G1) in
      let bs := border_set G1 ext in
      VSet.for_all (fun x => VSet.for_all (fun y => lsp G1 x y == lsp G2 x y) bs) bs.

    Lemma lsp_eq_is_full_extension (G1 G2 : t) :
      full_subgraph G1 G2 -> is_full_extension G1 G2.
    Proof.
      move=> hsub. unfold is_full_extension.
      set bs := (border_set _ _).
      assert (H : forall x, VSet.In x bs -> VSet.In x (V G1))
        by move=> ? /border_set_spec [? [_ [//]]].
      apply/VSet.for_all_spec=> x /H hx.
      apply/VSet.for_all_spec=> y /H hy.
      apply/ReflectEq.eqb_spec; apply: le_antisymm.
      2: by apply: lsp_dominate.
      unshelve apply: lsp_map_path2.
      * apply: subgraph_on_edge; exact hsub.
      * apply: vertices_sub; exact hsub.
      * move=> ??[??] /=; lia.
    Qed.

    Lemma is_full_extension_lsp_dominate (G1 G2 : t)
      `{invariants G1, invariants G2, acyclic_no_loop G2} :
      subgraph G1 G2 ->
      is_full_extension G1 G2 ->
      forall x y, VSet.In x (V G1) -> VSet.In y (V G1) ->
             (lsp G2 x y <= lsp G1 x y)%nbar.
    Proof.
      move=> hsub ext. pose proof (acG1 := subgraph_acyclic _ _ hsub _).
      apply: lsp_bound_extend_border=> x y hx hy.
      move: ext=> /VSet.for_all_spec/(_ x hx)/VSet.for_all_spec/(_ y hy).
      move=> /(@ReflectEq.eqb_spec _ reflectEq_nbar) ->; reflexivity.
    Qed.


    Lemma is_full_extension_spec (G1 G2 : t)
          `{invariants G1, invariants G2, acyclic_no_loop G2} :
      subgraph G1 G2 ->
      is_full_extension G1 G2
      <-> full_subgraph G1 G2.
    Proof.
      move=> sub; split.
      - move=> ext; constructor=> //; by apply: is_full_extension_lsp_dominate.
      - apply: lsp_eq_is_full_extension.
    Qed.

    (* Remove ? *)
    (* Defined for completeness, but clearly not what should be used in practice *)
    Definition is_full_subgraph (G1 G2 : t) : bool :=
      VSet.subset (V G1) (V G2) &&
        EdgeSet.subset (E G1) (E G2) &&
        (s G1 == s G2) &&
        VSet.for_all (fun x => VSet.for_all (fun y => lsp G1 x y == lsp G2 x y) (V G1)) (V G1).

    Lemma is_full_subgraph_spec G1 G2 :
      is_full_subgraph G1 G2 <-> full_subgraph G1 G2.
    Proof.
      unfold is_full_subgraph.
      split.
      - move=> /andP [] /andP [] /andP [] /VSet.subset_spec ?.
        move=> /EdgeSet.subset_spec ?.
        move=> /(@ReflectEq.eqb_spec _ reflectEq_vertices _ _) ?.
        move=> /VSet.for_all_spec h.
        constructor=> // v1 v2 inv1 inv2.
        move: (h v1 inv1)=> /VSet.for_all_spec /(_ v2  inv2).
        move=> /(@ReflectEq.eqb_spec _ reflectEq_nbar _ _) ->.
        apply: le_refl.
      - move=> sub. repeat try (apply/andP;split).
        + apply/VSet.subset_spec; apply: vertices_sub; exact sub.
        + apply/EdgeSet.subset_spec; apply: edges_sub; exact sub.
        + apply/eqb_specT; apply: same_src ; exact sub.
        + apply/VSet.for_all_spec=> x hx.
          apply/VSet.for_all_spec=> y hy.
          apply/eqb_specT. apply: le_antisymm.
          2: by apply: lsp_dominate.
          unshelve apply: lsp_map_path2.
          * apply: subgraph_on_edge; exact sub.
          * apply: vertices_sub; exact sub.
          * move=> ??[??] /=; lia.
    Qed.
  End IsFullSubgraph.

  Section ExtendLabelling.
    Context G1 G2 `{invariants G1, invariants G2}.
    Context l (HGl : correct_labelling G1 l)
            (embed : full_subgraph G1 G2)
            (acG2 : acyclic_no_loop G2).

    Let Gl := relabel_on G1 G2 l.
    Let l' := to_label ∘ (lsp Gl (s Gl)).

    Lemma extends_labelling x : VSet.In x (V G1) -> l' x = l x.
    Proof using Gl H H0 HGl acG2 embed.
      move=> xin1.
      destruct (source_pathOf G1 x xin1) as [[p _]].
      pose proof (lsp_eq := lsp_Gl_between_G1 G1 G2 l (edges_sub _ _ embed)
                               HGl (lsp_dominate _ _ embed)
                               _ _ (vertices_sub _ _ embed)
                               p (source_vertex G1) xin1).
      case: HGl=> [ls _].
      rewrite /l'/Gl /= -(same_src _ _  embed) lsp_eq /diff ls.
      replace (_ - _) with (Z.of_nat (l x)) by lia.
      apply: Nat2Z.inj; rewrite Z_of_to_label.
      move: (Zle_0_nat (l x))=> /Z.leb_spec0 -> //.
    Qed.

    Lemma relabel_on_correct_labelling : correct_labelling Gl l'.
    Proof using H H0 HGl acG2 embed.
      pose proof (invGl := relabel_on_invariants G1 G2 l
                                                 (edges_sub _ _ embed)
                                                 HGl).
      pose proof (acGl := acyclic_relabel_on G1 G2 l HGl
                                             (lsp_dominate _ _ embed)).
      apply: lsp_correctness. by apply/acyclic_no_loop_sloop.
    Qed.

    Lemma extends_correct_labelling : correct_labelling G2 l'.
    Proof using Gl H H0 HGl acG2 embed.
      case: relabel_on_correct_labelling => [sGl eGl].
      split=> //.
      move=> [[s w] t] ein.
      pose (e' := from2 G1 G2 l (edges_sub _ _ embed) (w ; ein)).
      epose (eGl (s, e'.π1, t) e'.π2).
      epose (weight_from2 G1 G2 l (edges_sub _ _ embed) HGl (w ; ein)).
      move: l0 g; cbn. lia.
    Qed.

  End ExtendLabelling.


  Lemma to_label_to_nat n : to_label (Some n) = Z.to_nat n.
  Proof. by []. Qed.

  Module RelabelWrtEdge.
  Section RelabelWrtEdge.
    Context G `{invG:invariants G} `{acG:acyclic_no_loop G}.

    Section BuildLabelling.
      Context l (Hl : correct_labelling G l).
      Context x (k : nat)
              (d := Some (Z.of_nat (k + l x)))
              (Hk : (lsp G x (s G) + d <= Some 0)%nbar).

      Definition r : labelling :=
        fun z => Nat.max (l z) (to_label (lsp G x z + d)%nbar).

      Lemma r_correct : correct_labelling G r.
      Proof using Hk Hl acG invG.
        case: Hl => Hl0 Hledge; split.
        - rewrite /r Hl0 Nat.max_0_l.
          move: Hk; move: (_ + _)%nbar=> [[|?|?]|] //=.
        - move=> e he. rewrite /r.
          set u := (u in Nat.max _ u).
          move: (Nat.max_dec (l e..s) u) => [->|/[dup] /Nat.max_r_iff ule ->].
          + etransitivity; first by apply: Hledge.
            apply: inj_le; apply: Nat.le_max_l.
          + destruct (edges_vertices G e he) as [hs ht].
            destruct e as [[s w] t].
            pose proof (h := lsp0_triangle_inequality G (V G) x s t w he hs).
            move: h ule; cbn. rewrite /d/u -/(lsp G x s) -/(lsp G x t).
            move: (Hledge _ he).
            all: cbn -[to_label] => //.
            case E: (to_label _).
            * etransitivity; last (apply: inj_le; apply: Nat.le_max_l); lia.
            * etransitivity; last (apply: inj_le; apply: Nat.le_max_r).
              rewrite -E.
              case: (lsp G x s) (lsp G x t) E h=> // ? [?|//].
              rewrite /d 2!to_label_to_nat /=.
              lia.
      Qed.
    End BuildLabelling.

    Section RelabelCoefs.
      Context (x y : V.t) (hx : VSet.In x (V G)) (hy : VSet.In y (V G))
              (nxy : Z) (hxy : (lsp G x y <= Some nxy)%nbar).
      Definition stdl : labelling := (fun x : V.t => to_label (lsp G (s G) x)).

      Definition dxy := Z.to_nat (Z.of_nat (stdl y) - Z.of_nat (stdl x) - nxy).

      Lemma dxy_bound :
        (lsp G x (s G) + Some (Z.of_nat (dxy + stdl x)) <= Some 0)%nbar.
      Proof using acG hx hxy hy invG.
        destruct (Z_of_to_label_s G x hx) as [nx [eqlspx [nxpos eqnx]]].
        destruct (Z_of_to_label_s G y hy) as [ny [eqlspy [nypos eqny]]].
        rewrite Nat2Z.inj_add /stdl add_finite eqnx add_assoc.
        rewrite /dxy /stdl eqnx eqny.
        pose proof (lsp_codistance G x (s G) y).
        pose proof (lsp_codistance G (s G) x (s G)).
        case E: (lsp G x (s G)) H H0 => //.
        rewrite ZifyInst.of_nat_to_nat_eq eqlspy eqlspx lsp_xx.
        move: hxy. case: (lsp G x y)=> // ?. cbn.
        lia.
      Qed.

      Definition l' := r stdl x dxy.

      Lemma l'_correct : correct_labelling G l'.
      Proof using acG hx hxy hy invG.
        apply: r_correct; [apply: lsp_correctness | apply: dxy_bound].
      Qed.


      Lemma to_label_add z k : (Some 0 <= z)%nbar -> (to_label z + k)%nat = to_label (z + Some (Z.of_nat k))%nbar.
      Proof using Type.
        move: z=> [[|?|?]|] //=; case: k=> //=; lia.
      Qed.

      Lemma to_label_mon z1 z2 : (z1 <= z2)%nbar -> (to_label z1 <= to_label z2)%nat.
      Proof using Type. move: z1 z2=> [[|?|?]|] [[|?|?]|] //=; lia. Qed.

      Lemma l'_on_x : l' x = (stdl x + dxy)%nat.
      Proof using acG hx invG.
        destruct (Z_of_to_label_s G x hx) as [nx [eqlspx [nxpos eqnx]]].
        rewrite /l'/r lsp_xx to_label_to_nat Nat2Z.id Nat.add_comm.
        apply: max_r; lia.
      Qed.

      Lemma l'_on_y : l' y = stdl y.
      Proof using acG hx hxy hy invG.
        apply: max_l; apply: to_label_mon.
        pose proof (lsp_codistance G (s G) x y); move: H hxy.
        destruct (Z_of_to_label_s G x hx) as [nx [eqlspx [nxpos eqnx]]].
        destruct (Z_of_to_label_s G y hy) as [ny [eqlspy [nypos eqny]]].
        rewrite /dxy /stdl Nat2Z.inj_add eqnx eqny eqlspx eqlspy .
        case E: (lsp _ _ _)=> [?|] //=.
        lia.
      Qed.

      Lemma l'_diff :
        Z.of_nat (l' y) - Z.of_nat (l' x) <= nxy.
      Proof using acG hx hxy hy invG.
        destruct (Z_of_to_label_s G x hx) as [nx [eqlspx [nxpos eqnx]]].
        destruct (Z_of_to_label_s G y hy) as [ny [eqlspy [nypos eqny]]].
        pose proof (lsp_codistance G (s G) x y); move: H hxy.
        rewrite l'_on_x l'_on_y Nat2Z.inj_add /dxy /stdl eqnx eqny eqlspx eqlspy.
        case E: (lsp _ _ _)=> [?|] //=; lia.
      Qed.

    End RelabelCoefs.

  End RelabelWrtEdge.
  End RelabelWrtEdge.

  Lemma labelling_ext_lsp
        G1 G2  `{acyclic_no_loop G1} `{invariants G1}
        (hext : forall l1, correct_labelling G1 l1 ->
                      exists l2, correct_labelling G2 l2 /\
                              (forall v, VSet.In v (V G1) -> l1 v = l2 v)) :
    forall vx vy, VSet.In vx (V G1) -> VSet.In vy (V G1) ->
             (lsp G2 vx vy <= lsp G1 vx vy)%nbar.
  Proof.
    move=> vx vy hvx hvy.
    case eqlsp2 : (lsp _ _ _)=> [nxy2|//].
    pose (n := match lsp G1 vx vy with
               | Some n => n
               | None => (nxy2  - 1)%Z end).
    assert (hbound : (lsp G1 vx vy <= Some n)%nbar)
      by (unfold n; case: (lsp _ _ _)=> //; reflexivity).
    pose proof (hl := RelabelWrtEdge.l'_correct _ vx vy hvx hvy _ hbound).
    move: (hext _ hl)=> [l' [hl' ll']].
    pose proof (hdiff := RelabelWrtEdge.l'_diff _ vx vy hvx hvy _ hbound).
    move: hdiff.  rewrite ll' // ll' // /n.
    pose proof (h := correct_labelling_lsp G2 eqlsp2 l' hl').
    case eqlsp1: (lsp _ _ _)=> [nxy1|]; first cbn; lia.
  Qed.
End WeightedGraph.

Module Type WeightedGraphSig (V : UsualOrderedType) (VSet : MSetInterface.S with Module E := V) := Nop <+ WeightedGraph V VSet.
