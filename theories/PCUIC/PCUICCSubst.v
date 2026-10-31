(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICInduction PCUICReduction PCUICClosed.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

(** * Closed single substitution:

    no lifting involved and one term at a time. *)

Local Ltac inv H := inversion H; subst.

Fixpoint csubst t k u :=
  match u with
  | tRel n =>
     match Nat.compare k n with
    | Datatypes.Eq => t
    | Gt => tRel n
    | Lt => tRel (Nat.pred n)
    end
  | tEvar ev args => tEvar ev (List.map (csubst t k) args)
  | tLambda na T M => tLambda na (csubst t k T) (csubst t (S k) M)
  | tApp u v => tApp (csubst t k u) (csubst t k v)
  | tProd na A B => tProd na (csubst t k A) (csubst t (S k) B)
  | tLetIn na b ty b' => tLetIn na (csubst t k b) (csubst t k ty) (csubst t (S k) b')
  | tCase ind p c brs =>
    let brs' := List.map (fun br => map_branch_k (csubst t) id k br) brs in
    tCase ind (map_predicate_k id (csubst t) k p)
      (csubst t k c) brs'
  | tProj p c => tProj p (csubst t k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (csubst t k) (csubst t k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (csubst t k) (csubst t k')) mfix in
    tCoFix mfix' idx
  | tPrim p => tPrim (map_prim (csubst t k) p)
  | x => x
  end.

(** It is equivalent to general substitution when substituting a closed term *)
Lemma closed_subst t k u : closed t ->
    csubst t k u = subst [t] k u.
Proof.
  revert k; induction u using term_forall_list_ind; intros k Hs;
    simpl; try f_equal; eauto with pcuic; solve_all.
  - destruct (PeanoNat.Nat.compare_spec k n).
    + subst k.
      rw PeanoNat.Nat.leb_refl Nat.sub_diag /=.
      now rw lift_closed.
    + destruct (leb_spec_Set k n); try lia.
      destruct (nth_error_spec [t] (n - k) ).
      simpl in l0; lia.
      now rw Nat.sub_1_r.
    + now destruct (Nat.leb_spec k n); try lia.
Qed.

(** It respects closedness of the substitutend as well. *)
Lemma closed_csubst t k u : closed t -> closedn (S k) u -> closedn k (csubst t 0 u).
Proof.
  intros.
  rw closed_subst; auto.
  eapply closedn_subst0. simpl. erewrite closed_upwards; eauto. lia.
  simpl. now rw Nat.add_1_r.
Qed.
