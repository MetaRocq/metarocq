
(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICSigmaCalculus.

From Equations.Type Require Import Relation_Properties.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma map2_set_binder_name_alpha_eq (nas : list aname) (Δ Δ' : PCUICEnvironment.context) :
  All2 (fun x y => x = (decl_name y)) nas Δ' ->
  eq_context_upto_names Δ Δ' ->
  (map2 set_binder_name nas Δ) = Δ'.
Proof.
  intros hl. induction 1 in nas, hl |- *; cbn; auto.
  destruct nas; cbn; auto.
  destruct nas; cbn; auto; depelim hl.
  f_equal; auto. destruct r; subst; cbn; auto.
Qed.
Abbreviation eq_names := (All2 (fun x y => x = (decl_name y))).

Lemma eq_names_subst_context nas Γ s k :
  eq_names nas Γ ->
  eq_names nas (subst_context s k Γ).
Proof.
  induction 1.
  * rewrite subst_context_nil. constructor.
  * rewrite subst_context_snoc. constructor; auto.
Qed.

Lemma eq_names_subst_instance nas Γ u :
  eq_names nas Γ ->
  eq_names nas (subst_instance u Γ).
Proof.
  induction 1.
  * constructor.
  * rewrite /subst_instance /=. constructor; auto.
Qed.

(* Lemma All2_compare_decls_subst pars n Γ i :
  eq_context_upto_names (subst_context pars n Γ@[i]) (subst_context pars n Γ'@[i])
  eq_context_upto_names (subst_context pars n Γ@[i]) (subst_context pars n Γ'@[i]) *)
Lemma alpha_eq_subst_instance Δ Δ' i :
  eq_context_upto_names Δ Δ' ->
  eq_context_upto_names Δ@[i] Δ'@[i].
Proof.
  induction 1.
  * constructor.
  * cbn. constructor; auto. destruct r; constructor; auto.
    all:cbn; subst; reflexivity.
Qed.


Lemma alpha_eq_context_assumptions Δ Δ' :
  eq_context_upto_names Δ Δ' ->
  context_assumptions Δ = context_assumptions Δ'.
Proof.
  induction 1; simpl; auto; try lia.
  destruct r; simpl; auto; lia.
Qed.

Lemma alpha_eq_extended_subst Δ Δ' k :
  eq_context_upto_names Δ Δ' ->
  extended_subst Δ k = extended_subst Δ' k.
Proof.
  induction 1 in k |- *; simpl; auto.
  destruct r; subst; simpl; auto. f_equal. apply IHX.
  rewrite IHX (alpha_eq_context_assumptions l l') //.
Qed.

Lemma alpha_eq_smash_context Δ Δ' :
  eq_context_upto_names Δ Δ' ->
  eq_context_upto_names (smash_context [] Δ) (smash_context [] Δ').
Proof.
  induction 1.
  * constructor.
  * destruct r; simpl; auto.
    rewrite !(smash_context_acc _ [_]).
    eapply All2_app; auto; repeat constructor; subst; simpl; auto.
    rewrite (All2_length X) -(alpha_eq_extended_subst l l' 0) // (alpha_eq_context_assumptions l l') //.
    now constructor.
Qed.

Lemma alpha_eq_lift_context n k Δ Δ' :
  eq_context_upto_names Δ Δ' ->
  eq_context_upto_names (lift_context n k Δ) (lift_context n k Δ').
Proof.
  induction 1.
  * constructor.
  * rewrite !lift_context_snoc; destruct x; depelim r; simpl; subst; auto;
    constructor; auto; repeat constructor; subst; simpl; auto;
    rewrite (All2_length X); now constructor.
Qed.

Lemma alpha_eq_subst_context s k Δ Δ' :
  eq_context_upto_names Δ Δ' ->
  eq_context_upto_names (subst_context s k Δ) (subst_context s k Δ').
Proof.
  induction 1.
  * constructor.
  * rewrite !subst_context_snoc; destruct x; depelim r; simpl; subst; auto;
    constructor; auto; repeat constructor; subst; simpl; auto;
    rewrite (All2_length X); now constructor.
Qed.

Lemma inst_case_predicate_context_eq {mdecl idecl ind p} :
  eq_context_upto_names p.(pcontext) (ind_predicate_context ind mdecl idecl) ->
  case_predicate_context ind mdecl idecl p =
  inst_case_predicate_context p.
Proof.
  intros a.
  eapply map2_set_binder_name_alpha_eq.
  { eapply eq_names_subst_context, eq_names_subst_instance.
    eapply All2_map_left. eapply All2_refl. reflexivity. }
  { apply alpha_eq_subst_context, alpha_eq_subst_instance.
    now symmetry. }
Qed.

Definition ind_binder ind idecl p :=
  let indty :=
    mkApps (tInd ind p.(puinst))
	    (map (lift0 #|ind_indices idecl|) p.(pparams) ++ to_extended_list (ind_indices idecl)) in
  {| decl_name := {|
               binder_name := nNamed (ind_name idecl);
               binder_relevance := ind_relevance idecl |};
  decl_body := None;
  decl_type := indty |}.

Definition case_predicate_context' ind mdecl idecl p :=
    ind_binder ind idecl p ::  subst_context (List.rev p.(pparams)) 0
    (subst_instance p.(puinst)
       (expand_lets_ctx (ind_params mdecl) (ind_indices idecl))).

Lemma eq_binder_annots_eq nas Γ :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Γ ->
  eq_context_upto_names (map2 set_binder_name nas Γ) Γ.
Proof.
  induction 1; simpl; constructor; auto.
  destruct x, y as [na [b|] ty]; simpl; constructor; auto.
Qed.


Definition pre_case_branch_context (ind : inductive) (mdecl : mutual_inductive_body)
  (params : list term) (puinst : Instance.t) (cdecl : constructor_body) :=
  subst_context (List.rev params) 0
  (expand_lets_ctx (subst_instance puinst (ind_params mdecl))
	 (subst_context (inds (inductive_mind ind) puinst (ind_bodies mdecl))
        #|ind_params mdecl|
        (subst_instance puinst (cstr_args cdecl)))).

Lemma pre_case_branch_context_length_args {ind mdecl params puinst cdecl} :
  #|pre_case_branch_context ind mdecl params puinst cdecl| = #|cstr_args cdecl|.
Proof.
  now rewrite /pre_case_branch_context; len.
Qed.

Lemma All2_eq_binder_subst_context (l : list (binder_annot name))  s k Γ :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l Γ ->
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l (subst_context s k Γ).
Proof.
  induction 1; rewrite ?subst_context_snoc //; constructor; auto.
Qed.

Lemma All2_eq_binder_subst_instance (l : list (binder_annot name)) u (Γ : context) :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l Γ ->
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l (subst_instance u Γ).
Proof.
  induction 1; rewrite ?subst_context_snoc //; constructor; auto.
Qed.

Lemma inst_case_branch_context_eq {ind mdecl cdecl p br} :
  eq_context_upto_names br.(bcontext) (cstr_branch_context ind mdecl cdecl) ->
  case_branch_context ind mdecl p (forget_types br.(bcontext)) cdecl = inst_case_branch_context p br.
Proof.
  intros.
  rewrite /case_branch_context /case_branch_context_gen.
  rewrite /inst_case_branch_context /inst_case_context.
  eapply map2_set_binder_name_alpha_eq.
  eapply eq_names_subst_context, eq_names_subst_instance.
  eapply All2_map_left. eapply All2_refl. reflexivity.
  rewrite /pre_case_branch_context_gen /inst_case_context.
  eapply alpha_eq_subst_context, alpha_eq_subst_instance.
  now symmetry.
Qed.
