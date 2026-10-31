From Stdlib Require Import Lia Arith Bool List Program.
From MetaRocq.Utils Require Import MRPrelude ReflectEq.
From Stdlib.ssr Require Import ssreflect.
From Equations Require Import Equations.
Import ListNotations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Class Listable T := { list_all : list T ; find_index : T -> nat ; cardinality := length list_all }.

Arguments find_index {T} {_} _.
Arguments list_all T {_}.
Arguments cardinality T {_}.

Class FinitelyListable T {l : Listable T}
  := { find_index_ok : forall t, nth_error (list_all T) (find_index t) = Some t
     ; enumerate_smallb : forallb  (fun '(n, t) => n == find_index t)
                            (combine (seq 0 (cardinality T)) (list_all T)) }.

Class FinitelyListablePackage T
  := { FinitelyListablePackage_Listable : Listable T
     ; FinitelyListablePackage_FinitelyListable : FinitelyListable T }.
#[export] Existing Instances FinitelyListablePackage_Listable FinitelyListablePackage_FinitelyListable.
#[global] Coercion FinitelyListablePackage_Listable : FinitelyListablePackage >-> Listable.
#[global] Coercion FinitelyListablePackage_FinitelyListable : FinitelyListablePackage >-> FinitelyListable.

Ltac prove_FinitelyListable :=
  split;
  [ let t := fresh in
    intro t; destruct t;
    vm_compute; try reflexivity
  | vm_compute; reflexivity ].

Ltac push_S_refine_num ev :=
  lazymatch ev with
  | S ?ev
    => refine (S _); push_S_refine_num ev
  | ?ev => let __ := open_constr:(eq_refl : ev = S _) in
           refine O
  end.

Ltac force_num ev :=
  lazymatch ev with
  | S ?ev => force_num ev
  | ?ev => unify ev O
  end.

Ltac partially_prove_Listable :=
  let fin := open_constr:(_) in
  unshelve esplit;
  [
  | repeat (let t := fresh in intro t; case t; clear t);
    push_S_refine_num fin ];
  force_num fin.

Ltac finish_prove_FinitelyListable :=
  split;
  [ cbv [list_all find_index];
    repeat (let t := fresh in intro t; case t; clear t);
    unshelve
      (repeat match goal with
              | [ |- nth_error (?x :: _) O = ?rhs ] => change (Some x = rhs)
              | [ |- nth_error (_ :: ?xs) (S ?n) = ?rhs ] => change (nth_error xs n = rhs)
              | [ |- nth_error ?ev _ = ?rhs ]
                => is_evar ev;
                   let __ := open_constr:(eq_refl : ev = cons _ _) in
                   idtac
              | [ |- Some _ = Some _ ] => reflexivity
              end);
    try exact nil
  | try instantiate (1:=nil) (* for empty types *);
    vm_compute; reflexivity ].

Ltac prove_ListableDerive :=
  lazymatch goal with
  | [ |- @FinitelyListable ?T ?H ]
    => instantiate (1:=ltac:(partially_prove_Listable)) in (value of H);
       cbv [H];
       finish_prove_FinitelyListable
  end.

Ltac prove_ListablePackage T :=
  refine (_ : { l : Listable T | FinitelyListable T });
  unshelve econstructor;
  [ partially_prove_Listable
  | finish_prove_FinitelyListable ].

Ltac prove_FinitelyListablePackage_goal _ :=
  unshelve econstructor;
  [ partially_prove_Listable
  | finish_prove_FinitelyListable ].
Ltac prove_FinitelyListablePackage T :=
  refine (_ : FinitelyListablePackage T);
  prove_FinitelyListablePackage_goal ().

Ltac get_ListablePackage T :=
  constr:(ltac:(prove_ListablePackage T)).

Section with_listable.
  Context {T}
          {Listable_T : Listable T}
          {FinitelyListable_T : FinitelyListable T}.

  Lemma find_index_iff x n : find_index x = n <-> List.nth_error (list_all T) n = Some x.
  Proof using FinitelyListable_T.
    split; [ intro; subst; apply find_index_ok | ].
    generalize enumerate_smallb.
    cbv [cardinality].
    set (offset := O).
    change n with (offset + n)%nat at 2.
    clearbody offset.
    rename x into v.
    intros Hfold Hnth; revert offset n Hfold Hnth.
    induction (list_all T) as [|x xs IHxs]; intros.
    { destruct n; cbn in *; congruence. }
    { cbn in *.
      move: Hfold; case: eqb_specT => //= Hfold1 Hfold2.
      specialize (IHxs (S offset) (pred n) Hfold2).
      subst offset; destruct n as [|n]; cbn in *.
      { inversion Hnth; subst; lia. }
      { specialize (IHxs Hnth); lia. } }
  Qed.

  Lemma enumerate_unique n m x y
        (Hn : List.nth_error (list_all T) n = Some x)
        (Hm : List.nth_error (list_all T) m = Some y)
        (Hxy : x = y)
    : n = m.
  Proof using FinitelyListable_T. rewrite <- !find_index_iff in *; subst; reflexivity. Qed.

  Lemma find_index_inj x y : find_index x = find_index y -> x = y.
  Proof using FinitelyListable_T. rw find_index_iff find_index_ok; congruence. Qed.

  Definition eqb_of_listable : T -> T -> bool := fun x y => Nat.eqb (find_index x) (find_index y).
  Lemma eqb_of_listable_refl x : eqb_of_listable x x = true.
  Proof using Type. cbv [eqb_of_listable]. apply Nat.eqb_refl. Qed.
  Lemma eqb_of_listable_lb x y : x = y -> eqb_of_listable x y = true.
  Proof using Type. intros; subst; apply eqb_of_listable_refl. Qed.
  Lemma eqb_of_listable_bl x y : eqb_of_listable x y = true -> x = y.
  Proof using FinitelyListable_T. cbv [eqb_of_listable]; rw Nat.eqb_eq. apply find_index_inj. Qed.
  Lemma eqb_of_listable_eq x y : eqb_of_listable x y = true <-> x = y.
  Proof using FinitelyListable_T. split; auto using eqb_of_listable_lb, eqb_of_listable_bl. Qed.
  Lemma eqb_of_listable_spec x y : reflectProp (x = y) (eqb_of_listable x y).
  Proof using FinitelyListable_T. generalize (eqb_of_listable_eq x y); case: eqb_of_listable; case; constructor; auto. Qed.

  #[local] Instance ReflectEq_of_listable : ReflectEq T
    := { eqb := eqb_of_listable
       ; eqb_spec := eqb_of_listable_spec }.
End with_listable.

#[export] Existing Instance ReflectEq_of_listable.

Local Obligation Tactic := try prove_FinitelyListablePackage_goal ().
#[export,program] Instance unit_FinitelyListablePackage : FinitelyListablePackage unit := _.
#[export,program] Instance Empty_set_FinitelyListablePackage : FinitelyListablePackage Empty_set := _.
#[export,program] Instance True_FinitelyListablePackage : FinitelyListablePackage True := _.
#[export,program] Instance False_FinitelyListablePackage : FinitelyListablePackage False := _.
#[export,program] Instance bool_FinitelyListablePackage : FinitelyListablePackage bool := _.
#[export] Instance byte_FinitelyListablePackage : FinitelyListablePackage Byte.byte.
Proof.
  unshelve econstructor.
  { unshelve esplit; [ | exact Byte.to_nat ].
    { let ls := (eval cbv in (List.flat_map (fun v => match Byte.of_nat v with Some v => [v] | None => [] end) (seq 0 256))) in
      exact ls. } }
  { split.
    { intro x; destruct x; vm_compute; reflexivity. }
    { vm_compute; reflexivity. } }
Defined.
