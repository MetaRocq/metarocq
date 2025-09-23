(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils NonEmptyLevelExprSet.

From MetaRocq.Common Require Universes.
From MetaRocq.Common Require Import LoopChecking.Common.
From Equations Require Import Equations.
Set Equations Transparent.

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

Module Type FMapOTInterface (E : UsualOrderedType).
  Module OT := FMapOrderedType_from_UsualOrderedType E.
  Include FMapInterface.Sfun OT.
End FMapOTInterface.

Module Q <: Quantity.
  Include OrdersEx.Z_as_OT.
  Import CommutativeMonoid.

  Instance comm_monoid : IsCommMonoid Z :=
    { zero := Z.zero ; one := 1%Z; add := Z.add }.

  Program Instance add_inj_eq z : Injective (Z.add z) eq eq.
  Next Obligation. unfold eq in *. lia. Qed.

  Program Instance add_inj_lt z : Injective (Z.add z) lt lt.
  Next Obligation. lia. Qed.

  Definition reflect_eq : ReflectEq t := _.
  Definition eq_leibniz x y : eq x y -> x = y := fun e => e.
End Q.

Module Type LevelSets.
  (* Signature of levels: decidable, ordered type *)
  Declare Module Level : OrderedTypeWithLeibnizWithReflect.
  Declare Module LevelSet : LevelSet_fun Level.
  Declare Module LevelExpr : LevelExprT Level Q.
  Declare Module LevelExprSet : LevelExprSet_fun Level Q LevelExpr.
  Declare Module LevelMap : FMapOTInterface Level.
  Module NES := NonEmptyLevelExprSet Level Q LevelSet LevelExpr LevelExprSet.
End LevelSets.

Module FromLevelSets (LS : LevelSets).
Export LS.

Import NES.OfQ.
Import NES.

#[export] Existing Instance Level.reflect_eq.
#[export] Existing Instance NES.reflect_eq.

Module LevelSetFact := WFactsOn Level LevelSet.
Module LevelSetProp := WPropertiesOn Level LevelSet.
Module LevelSetDecide := LevelSetProp.Dec.
Module LevelMapFact := FMapFacts.WProperties_fun LevelMap.OT LevelMap.

Declare Scope levels_scope.
Delimit Scope levels_scope with levels.
Bind Scope levels_scope with LevelSet.t.

Ltac lsets := LevelSetDecide.fsetdec.
Notation "(=_lset)" := LevelSet.Equal (at level 0) : levels_scope.
Infix "=_lset" := LevelSet.Equal (at level 30) : levels_scope.
Infix "⊂_lset" := LevelSet.Subset (at level 70) : levels_scope.
Infix "∪" := LevelSet.union (at level 70) : levels_scope.
Infix "=m" := LevelMap.Equal (at level 50) : levels_scope.
Notation "#| V |" := (LevelSet.cardinal V) : levels_scope.

Open Scope levels_scope.

Definition print_level_nat_map (m : LevelMap.t nat) :=
  let list := LevelMap.elements m in
  print_list (fun '(l, w) => Level.to_string l ^ " -> " ^ string_of_nat w) nl list.

Definition print_lset (l : LevelSet.t) :=
  let list := LevelSet.elements l in
  print_list Level.to_string " " list.

Module LevelExprSetFact := WFactsOn LevelExpr LevelExprSet.
Module LevelExprSetProp := WPropertiesOn LevelExpr LevelExprSet.

#[global] Instance levelexprset_eq_dec : Classes.EqDec LevelExprSet.t := Classes.eq_dec.

Derive NoConfusion for NES.t.

Module LevelExprSetDecide := WDecide (LevelExprSet).
Ltac lesets := LevelExprSetDecide.fsetdec.

Lemma levelset_not_Empty_is_empty s :
  LevelSet.is_empty s = false <-> ~ LevelSet.Empty s.
Proof.
  split.
  - intros H he. red in he. apply negbT in H. unshelve eapply (contraNnot _ H).
    3:exact he. intros ha. now apply LevelSetFact.is_empty_1.
  - intros ne. destruct LevelSet.is_empty eqn:he => //.
    eapply LevelSetFact.is_empty_2 in he. contradiction.
Qed.

Lemma in_singleton l : LevelSet.In l (LevelSet.singleton l).
Proof. lsets. Qed.

Lemma not_in_union_inv l ls ls' :
  ~ LevelSet.In l (LevelSet.union ls ls') ->
  ~ LevelSet.In l ls /\ ~ LevelSet.In l ls'.
Proof.
  rewrite LevelSet.union_spec. firstorder.
Qed.

Lemma levelmap_add_spec {A} (m m' : LevelMap.t A) {k v}:
  LevelMapFact.Add k v m m' ->
  m' =m LevelMap.add k v m.
Proof.
  trivial.
Qed.

Lemma not_empty_exists V : ~ LevelSet.Empty V -> exists l, LevelSet.In l V.
Proof.
  intros ne.
  destruct (LevelSet.choose V) eqn:ch. exists e.
  now eapply LevelSet.choose_spec1 in ch.
  now apply LevelSet.choose_spec2 in ch.
Qed.

Lemma diff_eq U V : LevelSet.diff V U =_lset V <-> LevelSet.inter V U =_lset LevelSet.empty.
Proof. split. lsets. lsets. Qed.

Lemma levelset_neq U V : LevelSet.equal U V = false -> ~ LevelSet.Equal U V.
Proof. intros eq heq % LevelSet.equal_spec. congruence. Qed.

Lemma levelset_union_same U : LevelSet.union U U =_lset U.
Proof. lsets. Qed.


Lemma LevelSet_In_elements l s :
  In l (LevelSet.elements s) <-> LevelSet.In l s.
Proof.
  rewrite LevelSetFact.elements_iff.
  now rewrite InA_In_eq.
Qed.

Lemma In_elements {x} {s : LevelExprSet.t} : LevelExprSet.In x s <-> List.In x (LevelExprSet.elements s).
Proof.
  split. now move/LevelExprSetFact.elements_1/InA_In_eq.
  now move/InA_In_eq/LevelExprSetFact.elements_2.
Qed.

Lemma not_mem l s : ~~ LevelSet.mem l s <-> ~ LevelSet.In l s.
Proof.
  split. apply contraNnot. apply LevelSet.mem_spec.
  eapply contra_notN; tea. now move/LevelSet.mem_spec.
Qed.

Definition non_W_atoms W (l : LevelExprSet.t) :=
  LevelExprSet.filter (fun lk => ~~ LevelSet.mem lk.1 W) l.

Lemma non_W_atoms_spec W l : forall x, LevelExprSet.In x (non_W_atoms W l) <-> LevelExprSet.In x l /\ ~ LevelSet.In x.1 W.
Proof.
  intros x. now rewrite /non_W_atoms LevelExprSet.filter_spec -not_mem.
Qed.

Lemma non_W_atoms_subset W l : non_W_atoms W l ⊂_leset l.
Proof. intros x. now rewrite /non_W_atoms LevelExprSet.filter_spec. Qed.

Lemma levels_exprs_non_W_atoms {W prem} :
  LevelSet.Equal (levels (non_W_atoms W prem)) (LevelSet.diff (levels prem) W).
Proof.
  intros e. unfold non_W_atoms.
  rewrite levels_spec LevelSet.diff_spec levels_spec.
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
    eapply levels_spec in hin as [k hin]. lesets.
  - intros emp l hin. eapply emp. eapply (levels_spec l.1). exists l.2.
    now destruct l.
Qed.

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

Lemma diff_cardinal_inter V W : #|LevelSet.diff V W| = #|V| - #|LevelSet.inter V W|.
Proof.
  pose proof (LevelSetProp.diff_inter_cardinal V W). lia.
Qed.

Lemma diff_cardinal V W : W ⊂_lset V -> #|LevelSet.diff V W| = #|V| - #|W|.
Proof.
  intros hsub.
  rewrite diff_cardinal_inter LevelSetProp.inter_sym LevelSetProp.inter_subset_equal //.
Qed.

End FromLevelSets.