
(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Lia MSetList OrderedTypeAlt OrderedTypeEx FMapAVL FMapFacts MSetAVL MSetFacts MSetProperties.
From MetaRocq.Utils Require Import utils MRMSets MRFSets.
From Stdlib Require Import ssreflect.
From Equations Require Import Equations.

Local Open Scope string_scope2.
Definition compare_ident := string_compare.

(** ** Reification of names ** *)

(** [Comment taken from Rocq's code]
    - Id.t is the type of identifiers, that is morally a subset of strings which
      only contains Unicode characters of the Letter kind (and a few more).
      => [ident]
    - Name.t is an ad-hoc variant of Id.t option allowing to handle optionally
      named objects.
      => [name]
    - DirPath.t represents generic paths as sequences of identifiers.
      => [dirpath]
    - Label.t is an equivalent of Id.t made distinct for semantical purposes.
      => [ident]
    - ModPath.t are module paths.
      => [modpath]
    - KerName.t are absolute names of objects in Rocq.
      => [kername]

    And also :
    - Constant.t => [kername]
    - variable => [ident]
    - MutInd.t => [kername]
    - inductive => [inductive]
    - constructor => [inductive * nat]
    - Projection.t => [projection]
    - GlobRef.t => global_reference

    Finally, we define the models of primitive types (uint63 and floats64).
*)

Definition ident   := string. (* e.g. nat *)
Definition qualid  := string. (* e.g. Datatypes.nat *)

(** Type of directory paths. Essentially a list of module identifiers. The
    order is reversed to improve sharing. E.g. A.B.C is ["C";"B";"A"] *)
Definition dirpath := list ident.

Module IdentOT := StringOT.
Module IdentOTOrig := OrdersAlt.Backport_OT IdentOT.

Module IdentSet := MSetAVL.Make IdentOT.
Module IdentSetFact := MSetFacts.WFactsOn IdentOT IdentSet.
Module IdentSetOrdProp := MSetProperties.OrdProperties IdentSet.
Module IdentSetProp := IdentSetOrdProp.P.
Module IdentSetDecide := IdentSetProp.Dec.
Module IdentSetExtraOrdProp := MSets.ExtraOrdProperties IdentSet IdentSetOrdProp.
Module IdentSetExtraDecide := MSetAVL.Decide IdentOT IdentSet.

Module IdentMap := FMapAVL.Make IdentOTOrig.
Module IdentMapFact := FMapFacts.WProperties IdentMap.
Module IdentMapExtraFact := FSets.WFactsExtra_fun IdentOTOrig IdentMap IdentMapFact.F.
Module IdentMapDecide := FMapAVL.Decide IdentOTOrig IdentMap.

Module DirPathOT := ListOrderedType IdentOT.
Module DirPathOTOrig := OrdersAlt.Backport_OT DirPathOT.

Module DirPathSet := MSetAVL.Make DirPathOT.
Module DirPathSetFact := MSetFacts.WFactsOn DirPathOT DirPathSet.
Module DirPathSetOrdProp := MSetProperties.OrdProperties DirPathSet.
Module DirPathSetProp := DirPathSetOrdProp.P.
Module DirPathSetDecide := DirPathSetProp.Dec.
Module DirPathSetExtraOrdProp := MSets.ExtraOrdProperties DirPathSet DirPathSetOrdProp.
Module DirPathSetExtraDecide := MSetAVL.Decide DirPathOT DirPathSet.

Module DirPathMap := FMapAVL.Make DirPathOTOrig.
Module DirPathMapFact := FMapFacts.WProperties DirPathMap.
Module DirPathMapExtraFact := FSets.WFactsExtra_fun DirPathOTOrig DirPathMap DirPathMapFact.F.
Module DirPathMapDecide := FMapAVL.Decide DirPathOTOrig DirPathMap.

#[global] Instance dirpath_eqdec : Classes.EqDec dirpath := _.

Definition string_of_dirpath (dp : dirpath) : string :=
  String.concat "." (List.rev dp).

(** The module part of the kernel name.
    - MPfile is for toplevel libraries, i.e. .vo files
    - MPbound are parameters of functors
    - MPdot is for submodules
*)
Inductive modpath :=
| MPfile  (dp : dirpath)
| MPbound (dp : dirpath) (id : ident) (i : nat)
| MPdot   (mp : modpath) (id : ident).
Derive NoConfusion for modpath.

Fixpoint string_of_modpath (mp : modpath) : string :=
  match mp with
  | MPfile dp => string_of_dirpath dp
  | MPbound dp id n => string_of_dirpath dp ^ "." ^ id ^ "." ^ string_of_nat n
  | MPdot mp id => string_of_modpath mp ^ "." ^ id
  end.

(** The absolute names of objects seen by kernel *)
Definition kername := modpath × ident.

Definition string_of_kername (kn : kername) :=
  string_of_modpath kn.1 ^ "." ^ kn.2.

(* Eval compute in DirPathOT.compare ["foo"; "bar"] ["baz"].
 *)

Module ModPathComp.
  Definition t := modpath.

  Definition eq := @eq modpath.
  Definition eq_univ : RelationClasses.Equivalence eq := _.

  Definition mpbound_compare dp id k dp' id' k' :=
    compare_cont (DirPathOT.compare dp dp')
      (compare_cont (IdentOT.compare id id') (Nat.compare k k')).

  Fixpoint compare mp mp' :=
    match mp, mp' with
    | MPfile dp, MPfile dp' => DirPathOT.compare dp dp'
    | MPbound dp id k, MPbound dp' id' k' =>
      mpbound_compare dp id k dp' id' k'
    | MPdot mp id, MPdot mp' id' =>
      compare_cont (compare mp mp') (IdentOT.compare id id')
    | MPfile _, _ => Gt
    | _, MPfile _ => Lt
    | MPbound _ _ _, _ => Gt
    | _, MPbound _ _ _ => Lt
    end.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma nat_compare_sym : forall x y, Nat.compare x y = CompOpp (Nat.compare y x).
  Proof.
    intros; apply PeanoNat.Nat.compare_antisym.
  Qed.

  Lemma compare_eq x y : (x ?= y) = Eq -> x = y.
  Proof.
    induction x in y |- *; destruct y; simpl; auto; try congruence.
    intros c. eapply DirPathOT.compare_eq in c; now subst.
    unfold mpbound_compare.
    destruct (DirPathOT.compare dp dp0) eqn:eq => //.
    destruct (IdentOT.compare id id0) eqn:eq' => //.
    destruct (Nat.compare i i0) eqn:eq'' => //.
    apply DirPathOT.compare_eq in eq.
    apply string_compare_eq in eq'.
    apply PeanoNat.Nat.compare_eq in eq''. congruence.
    destruct (x ?= y) eqn:eq; try congruence.
    specialize (IHx _ eq). subst.
    now intros c; apply string_compare_eq in c; subst.
    all:simpl; discriminate.
  Qed.

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto.
    apply DirPathOT.compare_sym.
    unfold mpbound_compare.
    rewrite DirPathOT.compare_sym.
    rewrite IdentOT.compare_sym.
    destruct (DirPathOT.compare dp dp0); auto.
    simpl. destruct (IdentOT.compare id id0); simpl; auto.
    apply nat_compare_sym.
    rewrite IHx.
    destruct (x ?= y); simpl; auto.
    apply IdentOT.compare_sym.
  Qed.

  Lemma nat_compare_trans :
    forall c x y z, Nat.compare x y = c -> Nat.compare y z = c -> Nat.compare x z = c.
  Proof.
    intros c x y z.
    destruct (PeanoNat.Nat.compare_spec x y); subst; intros <-;
    destruct (PeanoNat.Nat.compare_spec y z); subst; try congruence;
    destruct (PeanoNat.Nat.compare_spec x z); subst; try congruence; lia.
  Qed.

  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
    intros c x y z. revert c.
    induction x in y, z |- *; destruct y, z; intros c; simpl; auto; try congruence.
    apply DirPathOT.compare_trans.
    unfold mpbound_compare.
    eapply compare_cont_trans; eauto using DirPathOT.compare_trans, DirPathOT.compare_eq.
    intros c'.
    eapply compare_cont_trans; eauto using StringOT.compare_trans, StringOT.compare_eq, nat_compare_trans.
    intros x y. apply StringOT.compare_eq.
    destruct (x ?= y) eqn:eq.
    apply compare_eq in eq. subst.
    destruct (IdentOT.compare id id0) eqn:eq.
    apply string_compare_eq in eq; red in eq; subst. all:intros <-; auto.
    destruct (y ?= z) eqn:eq'; auto.
    apply compare_eq in eq'; subst.
    intros eq'.
    eapply IdentOT.compare_trans; eauto. cbn in *.
    destruct (y ?= z) eqn:eq'; auto. cbn.
    now apply IdentOT.compare_trans.
    destruct (y ?= z) eqn:eq'; auto; cbn; try congruence.
    apply compare_eq in eq'; subst.
    intros eq'. now rewrite eq.
    rewrite (IHx _ _ _ eq eq') //.
    destruct (y ?= z) eqn:eq'; cbn; auto; try congruence.
    apply compare_eq in eq'; subst.
    intros eq'. now rewrite eq.
    now rewrite (IHx _ _ _ eq eq').
  Qed.

End ModPathComp.

Module ModPathOT := OrderedType_from_Alt ModPathComp.
Module ModPathOTNew := OrdersAlt.Update_OT ModPathOT.

Module ModPathSet := MSetAVL.Make ModPathOTNew.
Module ModPathSetFact := MSetFacts.WFactsOn ModPathOTNew ModPathSet.
Module ModPathSetOrdProp := MSetProperties.OrdProperties ModPathSet.
Module ModPathSetProp := ModPathSetOrdProp.P.
Module ModPathSetDecide := ModPathSetProp.Dec.
Module ModPathSetExtraOrdProp := MSets.ExtraOrdProperties ModPathSet ModPathSetOrdProp.
Module ModPathSetExtraDecide := MSetAVL.Decide ModPathOTNew ModPathSet.

Module ModPathMap := FMapAVL.Make ModPathOT.
Module ModPathMapFact := FMapFacts.WProperties ModPathMap.
Module ModPathMapExtraFact := FSets.WFactsExtra_fun ModPathOT ModPathMap ModPathMapFact.F.
Module ModPathMapDecide := FMapAVL.Decide ModPathOT ModPathMap.

Program Definition modpath_eq_dec (x y : modpath) : { x = y } + { x <> y } :=
  match ModPathComp.compare x y with
  | Eq => left _
  | _ => right _
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  now eapply ModPathComp.compare_eq in Heq_anonymous.
Qed.
Next Obligation.
  match goal with [ H : _ <> _ |- _ ] => pose proof ModPathOT.eq_refl end. congruence.
Qed.

#[global] Instance modpath_EqDec : Classes.EqDec modpath := { eq_dec := modpath_eq_dec }.

Module KernameComp.
  Definition t := kername.

  Definition eq := @eq kername.
  Lemma eq_equiv : RelationClasses.Equivalence eq.
  Proof. apply _. Qed.

  Definition compare kn kn' :=
    match kn, kn' with
    | (mp, id), (mp', id') =>
      compare_cont (ModPathComp.compare mp mp') (IdentOT.compare id id')
    end.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto.
    unfold compare_ident.
    rewrite ModPathComp.compare_sym IdentOT.compare_sym.
    destruct ModPathComp.compare, IdentOT.compare; auto.
  Qed.

  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
    intros c [] [] [] => /=.
    eapply compare_cont_trans; eauto using ModPathComp.compare_trans, ModPathComp.compare_eq,
      StringOT.compare_trans.
  Qed.

End KernameComp.

Module Kername.
 Include KernameComp.
 Module OT := OrderedType_from_Alt KernameComp.

 Definition lt := OT.lt.
 Global Instance lt_strorder : StrictOrder OT.lt.
  Proof.
    constructor.
    - intros x X. apply OT.lt_not_eq in X. apply X. apply OT.eq_refl.
    - intros x y z X1 X2. eapply OT.lt_trans; eauto.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) OT.lt.
  Proof.
    intros x x' H1 y y' H2.
    red in H1, H2. subst. reflexivity.
  Qed.

  Definition compare_spec : forall x y, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    induction x; destruct y.
    simpl.
    destruct (ModPathComp.compare a m) eqn:eq.
    destruct (IdentOT.compare b i) eqn:eq'.
    all:constructor. red. eapply ModPathComp.compare_eq in eq. eapply string_compare_eq in eq'. congruence.
    all:hnf; simpl; rewrite ?eq ?eq' //.
    rewrite ModPathComp.compare_sym eq /= IdentOT.compare_sym eq' //.
    now rewrite ModPathComp.compare_sym eq /=.
  Defined.

  Lemma compare_eq x y : compare x y = Eq <-> x = y.
  Proof.
    split.
    - destruct (compare_spec x y); try congruence.
    - intros <-. destruct (compare_spec x x); auto.
      now apply irreflexivity in H.
      now apply irreflexivity in H.
  Qed.

  Definition eqb kn kn' :=
    match compare kn kn' with
    | Eq => true
    | _ => false
    end.

  #[global, program] Instance reflect_kername : ReflectEq kername := {
    eqb := eqb
  }.
  Next Obligation.
    unfold eqb. destruct compare eqn:e; constructor.
    - now apply compare_eq in e.
    -intros e'; subst. now rewrite OT.eq_refl in e.
    -intros e'; subst. now rewrite OT.eq_refl in e.
  Defined.

  Definition eq_dec : forall (x y : t), { x = y } + { x <> y } := Classes.eq_dec.

End Kername.

Module KernameMap := FMapAVL.Make Kername.OT.
Module KernameMapFact := FMapFacts.WProperties KernameMap.
Module KernameMapExtraFact := FSets.WFactsExtra_fun Kername.OT KernameMap KernameMapFact.F.
Module KernameMapDecide := FMapAVL.Decide Kername.OT KernameMap.

Abbreviation eq_kername := (eqb (A:=kername)) (only parsing).

Lemma eq_kername_refl kn : eq_kername kn kn.
Proof.
  eapply ReflectEq.eqb_refl.
Qed.

Definition eq_constant := eq_kername.

(* Local Open Scope string_scope.*)
(* Eval compute in KernameOT.compare (MPfile ["fdejrkjl"], "A") (MPfile ["lfrk;k"], "B"). *)

Module KernameSet := MSetAVL.Make Kername.
Module KernameSetFact := MSetFacts.WFactsOn Kername KernameSet.
Module KernameSetOrdProp := MSetProperties.OrdProperties KernameSet.
Module KernameSetProp := KernameSetOrdProp.P.
Module KernameSetDecide := KernameSetProp.Dec.
Module KernameSetExtraOrdProp := MSets.ExtraOrdProperties KernameSet KernameSetOrdProp.
Module KernameSetExtraDecide := MSetAVL.Decide Kername KernameSet.

Lemma knset_in_fold_left {A} kn f (l : list A) acc :
  KernameSet.In kn (fold_left (fun acc x => KernameSet.union (f x) acc) l acc) <->
  (KernameSet.In kn acc \/ exists a, In a l /\ KernameSet.In kn (f a)).
Proof.
  induction l in acc |- *; simpl.
  - split; auto. intros [H0|H0]; auto. now destruct H0.
  - rewrite IHl. rewrite KernameSet.union_spec.
    intuition auto.
    * right. now exists a; intuition auto.
    * destruct H0 as [a' [ina inkn]].
      right. now exists a'; intuition auto.
    * destruct H0 as [a' [ina inkn]].
      destruct ina as [<-|ina'];
      intuition auto. right. now exists a'.
Qed.

(** Designation of a (particular) inductive type. *)
Record inductive : Set := mkInd { inductive_mind : kername ;
                                  inductive_ind : nat }.
Arguments mkInd _%_bs _%_nat.

Derive NoConfusion for inductive.

Definition string_of_inductive (i : inductive) :=
  string_of_kername (inductive_mind i) ^ "," ^ string_of_nat (inductive_ind i).

Definition eq_inductive_def i i' :=
  let 'mkInd i n := i in
  let 'mkInd i' n' := i' in
  eqb (i, n) (i', n').

#[global, program] Instance reflect_eq_inductive : ReflectEq inductive := {
  eqb := eq_inductive_def
}.
Next Obligation.
  destruct x as [m n], y as [m' n']; cbn -[eqb].
  case: eqb_spec ; nodec.
  cbn. constructor. noconf p; reflexivity.
Qed.

Abbreviation eq_inductive := (eqb (A:=inductive)).

Lemma eq_inductive_refl i : eq_inductive i i.
Proof.
  apply ReflectEq.eqb_refl.
Qed.

Record projection := mkProjection
  { proj_ind : inductive;
    proj_npars : nat; (* Number of (non-let) parameters *)
    proj_arg : nat (* Argument to project *) }.

Definition eq_projection (p p' : projection) :=
  (p.(proj_ind), p.(proj_npars), p.(proj_arg)) == (p'.(proj_ind), p'.(proj_npars), p'.(proj_arg)).

#[global, program] Instance reflect_eq_projection : ReflectEq projection := {
  eqb := eq_projection
}.
Next Obligation.
  unfold eq_projection.
  case: eqb_spec ; nodec. destruct x, y; cbn.
  now constructor.
Qed.

Lemma eq_projection_refl i : eq_projection i i.
Proof.
  apply ReflectEq.eqb_refl.
Qed.

(** Kernel declaration references [global_reference] *)
Inductive global_reference :=
| VarRef : ident -> global_reference
| ConstRef : kername -> global_reference
| IndRef : inductive -> global_reference
| ConstructRef : inductive -> nat -> global_reference.

Derive NoConfusion for global_reference.

Definition string_of_gref gr : string :=
  match gr with
  | VarRef v => v
  | ConstRef s => string_of_kername s
  | IndRef (mkInd s n) =>
    "Inductive " ^ string_of_kername s ^ " " ^ (string_of_nat n)
  | ConstructRef (mkInd s n) k =>
    "Constructor " ^ string_of_kername s ^ " " ^ (string_of_nat n) ^ " " ^ (string_of_nat k)
  end.

Definition gref_eqb (x y : global_reference) : bool :=
  match x, y with
  | VarRef i, VarRef i' => eqb i i'
  | ConstRef c, ConstRef c' => eqb c c'
  | IndRef i, IndRef i' => eqb i i'
  | ConstructRef i k, ConstructRef i' k' => eqb i i' && eqb k k'
  | _, _ => false
  end.

#[global, program] Instance grep_reflect_eq : ReflectEq global_reference :=
  {| eqb := gref_eqb |}.
Next Obligation.
  destruct x, y; cbn; try constructor; try congruence.
  - destruct (eqb_spec i i0); constructor; subst; auto; congruence.
  - destruct (eqb_spec k k0); constructor; subst; auto; congruence.
  - destruct (eqb_spec i i0); constructor; subst; auto; congruence.
  - destruct (eqb_spec i i0); subst; cbn; auto; try constructor; try congruence.
    destruct (eqb_spec n n0); constructor; subst; congruence.
Defined.

Definition gref_eq_dec (gr gr' : global_reference) : {gr = gr'} + {~ gr = gr'} := Classes.eq_dec gr gr'.

#[global] Hint Resolve Kername.eq_dec : eq_dec.
