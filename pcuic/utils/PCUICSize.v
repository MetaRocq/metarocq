(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst.
From Stdlib Require Import ssreflect.

Definition def_size (size : term -> nat) (x : def term)
  := size (dtype x) + size (dbody x).

Definition mfixpoint_size (size : term -> nat) (l : mfixpoint term) :=
  list_size (def_size size) l.

Definition decl_size (size : term -> nat) (x : context_decl) :=
  size (decl_type x) + option_default size (decl_body x) 0.

Definition context_size (size : term -> nat) (l : context) :=
  list_size (decl_size size) l.

Definition branch_size (size : term -> nat) (br : branch term) :=
  context_size size br.(bcontext) + size br.(bbody).

Definition predicate_size (size : term -> nat) (p : PCUICAst.predicate term) :=
  list_size size p.(pparams) +
  context_size size p.(pcontext) +
  size p.(preturn).

Definition prim_size (size : term -> nat) (p : prim_val) : nat :=
  match p.π2 return nat with
  | primIntModel f => 0
  | primFloatModel f => 0
  | primStringModel s => 0
  | primArrayModel a => size a.(array_type) + size a.(array_default) + list_size size a.(array_value)
  end.

Fixpoint size t : nat :=
  match t with
  | tRel i => 1
  | tEvar ev args => S (list_size size args)
  | tLambda na T M => S (size T + size M)
  | tApp u v => S (size u + size v)
  | tProd na A B => S (size A + size B)
  | tLetIn na b t b' => S (size b + size t + size b')
  | tCase ind p c brs => S (predicate_size size p +
    size c + list_size (branch_size size) brs)
  | tProj p c => S (size c)
  | tFix mfix idx => S (mfixpoint_size size mfix)
  | tCoFix mfix idx => S (mfixpoint_size size mfix)
  | tPrim p => S (prim_size size p)
  | _ => 1
  end.

Lemma size_mkApps f l : size (mkApps f l) = size f + list_size size l.
Proof.
  induction l in f |- *; simpl; try lia.
  rw IHl. simpl. lia.
Qed.

Lemma nth_error_size {A} (f : A -> nat) {l : list A} {n x} :
  nth_error l n = Some x ->
  f x < list_size f l.
Proof.
  induction l in n |- *; destruct n; simpl => //; auto.
  - intros [= <-]. lia.
  - intros hnth. specialize (IHl _ hnth). lia.
Qed.
