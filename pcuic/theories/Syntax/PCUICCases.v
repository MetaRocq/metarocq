(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Reflect.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils.
Import Reflect. (* Reflect.eqb has priority over String.eqb *)

From Stdlib Require Import ssreflect.
From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
Set Equations Transparent.
Set Default Goal Selector "!".

Coercion ci_ind : case_info >-> inductive.

(** * Functions related to the "compact" case representation *)

Definition ind_subst mdecl ind u := inds (inductive_mind ind) u (ind_bodies mdecl).

Lemma inds_length ind u l : #|inds ind u l| = #|l|.
Proof.
  unfold inds. induction l; simpl; congruence.
Qed.
#[global]
Hint Rewrite inds_length : len.

Lemma inds_spec ind u l :
  inds ind u l = List.rev (mapi (fun i _ => tInd {| inductive_mind := ind; inductive_ind := i |} u) l).
Proof.
  unfold inds, mapi. induction l using rev_ind.
  - simpl. reflexivity.
  - now rewrite length_app /= Nat.add_1_r /= IHl mapi_rec_app /= rev_app_distr /= Nat.add_0_r.
Qed.

Definition ind_predicate_context ind mdecl idecl : context :=
  let ictx := (expand_lets_ctx mdecl.(ind_params) idecl.(ind_indices)) in
  let indty := mkApps (tInd ind (abstract_instance mdecl.(ind_universes)))
    (to_extended_list (smash_context [] mdecl.(ind_params) ,,, ictx)) in
  let inddecl :=
    {| decl_name :=
      {| binder_name := nNamed (ind_name idecl); binder_relevance := idecl.(ind_relevance) |};
       decl_body := None;
       decl_type := indty |}
  in (inddecl :: ictx).

Lemma ind_predicate_context_length ind mdecl idecl :
  #|ind_predicate_context ind mdecl idecl| = S #|idecl.(ind_indices)|.
Proof. now rewrite /ind_predicate_context /=; len. Qed.
#[global]
Hint Rewrite ind_predicate_context_length : len.

Definition inst_case_context params puinst (pctx : context) :=
  subst_context (List.rev params) 0 (subst_instance puinst pctx).

Lemma inst_case_context_length params puinst pctx :
  #|inst_case_context params puinst pctx| = #|pctx|.
Proof. rewrite /inst_case_context. now len. Qed.
#[global]
Hint Rewrite inst_case_context_length : len.

Lemma inst_case_context_assumptions params puinst pctx :
  context_assumptions (inst_case_context params puinst pctx) =
  context_assumptions pctx.
Proof. rewrite /inst_case_context. now len. Qed.
#[global]
Hint Rewrite inst_case_context_assumptions : len.

Definition inst_case_predicate_context (p : predicate term) :=
  inst_case_context p.(pparams) p.(puinst) p.(pcontext).

Lemma inst_case_predicate_context_length p :
  #|inst_case_predicate_context p| = #|p.(pcontext)|.
Proof. rewrite /inst_case_predicate_context. now len. Qed.

Definition inst_case_branch_context (p : predicate term) (br : branch term) :=
  inst_case_context p.(pparams) p.(puinst) br.(bcontext).

Lemma inst_case_branch_context_length p br :
  #|inst_case_branch_context p br| = #|br.(bcontext)|.
Proof. rewrite /inst_case_branch_context. now len. Qed.

Definition iota_red npar p args br :=
  subst (List.rev (List.skipn npar args)) 0
    (expand_lets (inst_case_branch_context p br) (bbody br)).

Definition pre_case_predicate_context_gen ind mdecl idecl params puinst : context :=
  inst_case_context params puinst (ind_predicate_context ind mdecl idecl).

Definition case_predicate_context_gen ind mdecl idecl params puinst pctx :=
  map2 set_binder_name pctx (pre_case_predicate_context_gen ind mdecl idecl params puinst).

Definition case_predicate_context ind mdecl idecl p : context :=
  case_predicate_context_gen ind mdecl idecl p.(pparams) p.(puinst) (forget_types p.(pcontext)).
Arguments case_predicate_context _ _ _ !_.

Definition cstr_branch_context ind mdecl cdecl : context :=
  expand_lets_ctx mdecl.(ind_params)
    (subst_context (inds (inductive_mind ind) (abstract_instance mdecl.(ind_universes))
       mdecl.(ind_bodies)) #|mdecl.(ind_params)|
      cdecl.(cstr_args)).

Lemma cstr_branch_context_length ind mdecl cdecl :
  #|cstr_branch_context ind mdecl cdecl| = #|cdecl.(cstr_args)|.
Proof. rewrite /cstr_branch_context. now len. Qed.
#[global]
Hint Rewrite cstr_branch_context_length : len.

Lemma cstr_branch_context_assumptions ci mdecl cdecl :
  context_assumptions (cstr_branch_context ci mdecl cdecl) =
  context_assumptions (cstr_args cdecl).
Proof.
  rewrite /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx.
  now do 2 rewrite !context_assumptions_subst_context ?context_assumptions_lift_context.
Qed.

Definition pre_case_branch_context_gen ind mdecl cdecl params puinst : context :=
  inst_case_context params puinst (cstr_branch_context ind mdecl cdecl).

Definition case_branch_context_gen ind mdecl params puinst pctx cdecl :=
  map2 set_binder_name pctx (pre_case_branch_context_gen ind mdecl cdecl params puinst).

Definition case_branch_context ind mdecl p bctx cdecl : context :=
  case_branch_context_gen ind mdecl p.(pparams) p.(puinst) bctx cdecl.
Arguments case_branch_context _ _ _ !_.
(*
Definition case_branch_context_gen ind mdecl params puinst bctx cdecl : context :=
  subst_context (List.rev params) 0
  (expand_lets_ctx (subst_instance puinst mdecl.(ind_params))
    (* We expand the lets in the context of parameters before
      substituting the actual parameters *)
    (subst_context (inds (inductive_mind ind) puinst mdecl.(ind_bodies)) #|mdecl.(ind_params)|
    (subst_instance puinst
      (map2 set_binder_name bctx cdecl.(cstr_args))))).

Definition case_branch_context ind mdecl p bctx cdecl : context :=
  case_branch_context_gen ind mdecl p.(pparams) p.(puinst) bctx cdecl.
Arguments case_branch_context _ _ _ _ !_. *)

Definition case_branches_contexts_gen ind mdecl idecl params puinst brs : list context :=
  map2 (case_branch_context_gen ind mdecl params puinst) brs idecl.(ind_ctors).

Definition case_branches_contexts ind mdecl idecl p brs : list context :=
  map2 (case_branch_context_gen ind mdecl p.(pparams) p.(puinst)) brs idecl.(ind_ctors).

Definition case_branch_type_gen ind mdecl (idecl : one_inductive_body) params puinst bctx ptm i cdecl : context * term :=
  let cstr := tConstruct ind i puinst in
  let args := to_extended_list cdecl.(cstr_args) in
  let cstrapp := mkApps cstr (map (lift0 #|cdecl.(cstr_args)|) params ++ args) in
  let brctx := case_branch_context_gen ind mdecl params puinst bctx cdecl in
  let upars := subst_instance puinst mdecl.(ind_params) in
  let indices :=
    (map (subst (List.rev params) #|cdecl.(cstr_args)|)
      (map (expand_lets_k upars #|cdecl.(cstr_args)|)
        (map (subst (inds (inductive_mind ind) puinst mdecl.(ind_bodies))
                    (#|mdecl.(ind_params)| + #|cdecl.(cstr_args)|))
          (map (subst_instance puinst) cdecl.(cstr_indices))))) in
  let ty := mkApps (lift0 #|cdecl.(cstr_args)| ptm) (indices ++ [cstrapp]) in
  (brctx, ty).

Definition case_branch_type ind mdecl idecl p (b : branch term) ptm i cdecl : context * term :=
  case_branch_type_gen ind mdecl idecl p.(pparams) p.(puinst) (forget_types b.(bcontext)) ptm i cdecl.
Arguments case_branch_type _ _ _ _ _ _ _ !_.

Lemma case_branch_type_fst ci mdecl idecl p br ptm c cdecl :
  (case_branch_type ci mdecl idecl p br ptm c cdecl).1 =
  (case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl).
Proof. reflexivity. Qed.

(* Definition case_branches_types_gen ind mdecl idecl params puinst ptm : list (context * term) :=
  mapi (case_branch_type_gen ind mdecl idecl params puinst ptm) idecl.(ind_ctors).

Definition case_branches_types ind mdecl idecl p ptm : list (context * term) :=
  mapi (case_branch_type_gen ind mdecl idecl p.(pparams) p.(puinst) ptm) idecl.(ind_ctors). *)

Lemma map2_length {A B C} (l : list A) (l' : list B) (f : A -> B -> C) : #|l| = #|l'| ->
  #|map2 f l l'| = #|l|.
Proof.
  induction l in l' |- *; destruct l' => /= //.
  intro eq; apply Nat.succ_inj in eq. now rewrite IHl.
Qed.

Lemma map2_set_binder_name_context_assumptions
  (l : list aname) (l' : context) : #|l| = #|l'| ->
  context_assumptions (map2 set_binder_name l l') = context_assumptions l'.
Proof.
  induction l in l' |- *; destruct l' => /= //.
  intro eq; apply Nat.succ_inj in eq. now rewrite IHl.
Qed.

Definition idecl_binder idecl :=
  {| decl_name :=
    {| binder_name := nNamed idecl.(ind_name);
        binder_relevance := idecl.(ind_relevance) |};
     decl_body := None;
     decl_type := idecl.(ind_type) |}.

Definition wf_predicate_gen mdecl idecl (pparams : list term) (pcontext : list aname) : Prop :=
  let decl := idecl_binder idecl in
  (#|pparams| = mdecl.(ind_npars)) /\
  (Forall2 (fun na decl => eq_binder_annot na decl.(decl_name))
    pcontext (decl :: idecl.(ind_indices))).

Definition wf_predicate mdecl idecl (p : predicate term) : Prop :=
  wf_predicate_gen mdecl idecl p.(pparams) (forget_types p.(pcontext)).

Definition wf_predicateb mdecl idecl (p : predicate term) : bool :=
  let decl := idecl_binder idecl in
  eqb #|p.(pparams)| mdecl.(ind_npars)
  && forallb2 (fun na decl => eqb_binder_annot na decl.(decl_name))
    (forget_types p.(pcontext)) (decl :: idecl.(ind_indices)).

Lemma wf_predicateP mdecl idecl p : reflectProp (wf_predicate mdecl idecl p) (wf_predicateb mdecl idecl p).
Proof.
  rewrite /wf_predicate /wf_predicate_gen /wf_predicateb.
  case: ReflectEq.eqb_spec => eqpars /= //.
  * case: (forallb2P _ _ (forget_types (pcontext p)) (idecl_binder idecl :: ind_indices idecl)
      (fun na decl => eqb_annot_reflect na decl.(decl_name))); constructor => //.
    intros [_ Hi]; contradiction.
  * constructor; intros [H _]; contradiction.
Qed.

Definition wf_branch_gen cdecl (bctx : list aname) : Prop :=
  (Forall2 (fun na decl => eq_binder_annot na decl.(decl_name))
    bctx cdecl.(cstr_args)).

Definition wf_branch cdecl (b : branch term) : Prop :=
  wf_branch_gen cdecl (forget_types b.(bcontext)).

Definition wf_branchb cdecl (b : branch term) : bool :=
  forallb2 (fun na decl => eqb_binder_annot na decl.(decl_name)) (forget_types b.(bcontext)) cdecl.(cstr_args).

Lemma wf_branchP cdecl b : reflect (wf_branch cdecl b) (wf_branchb cdecl b).
Proof.
  rewrite /wf_branch /wf_branch_gen /wf_branchb.
  apply (forallb2P _ _ (forget_types (bcontext b)) (cstr_args cdecl)
    (fun na decl => eqb_annot_reflect na decl.(decl_name))).
Qed.

Definition wf_branches_gen (ctors : list constructor_body) (brs : list (list aname)) : Prop :=
  Forall2 wf_branch_gen ctors brs.

Definition wf_branches idecl (brs : list (branch term)) : Prop :=
  Forall2 wf_branch idecl.(ind_ctors) brs.

Definition wf_branchesb idecl (brs : list (branch term)) : bool :=
  forallb2 wf_branchb idecl.(ind_ctors) brs.

Lemma wf_branchesP idecl brs : reflect (wf_branches idecl brs) (wf_branchesb idecl brs).
Proof.
  rewrite /wf_branches /wf_branches_gen /wf_branchesb.
  apply (forallb2P _ _ _ _ wf_branchP).
Qed.

#[global]
Hint Rewrite expand_lets_ctx_length : len.

Lemma case_predicate_context_length {ci mdecl idecl p} :
  wf_predicate mdecl idecl p ->
  #|case_predicate_context (ci_ind ci) mdecl idecl p| = #|p.(pcontext)|.
Proof.
  intros hl.
  unfold case_predicate_context, case_predicate_context_gen, pre_case_predicate_context_gen.
  rewrite map2_length /= //.
  2:len => //.
  destruct hl.
  rewrite (Forall2_length H0). len. now len.
Qed.

Lemma case_predicate_context_length_indices {ci mdecl idecl p} :
  wf_predicate mdecl idecl p ->
  #|case_predicate_context (ci_ind ci) mdecl idecl p| = S #|idecl.(ind_indices)|.
Proof.
  intros hl.
  unfold case_predicate_context, case_predicate_context_gen, pre_case_predicate_context_gen.
  pose proof (Forall2_length (proj2 hl)). simpl in H.
  rewrite -H.
  rewrite map2_length; len. all:len.
  - now len in H.
  - now len in H.
Qed.

Lemma wf_predicate_length_pars {mdecl idecl p} :
  wf_predicate mdecl idecl p ->
  #|p.(pparams)| = ind_npars mdecl.
Proof.
  now intros [].
Qed.

Lemma wf_predicate_length_pcontext {mdecl idecl p} :
  wf_predicate mdecl idecl p ->
  #|p.(pcontext)| = S #|ind_indices idecl|.
Proof.
  intros [].
  pose proof (Forall2_length H0). now len in H1.
Qed.

Lemma wf_branch_length {cdecl br} :
  wf_branch cdecl br ->
  #|br.(bcontext)| = #|cstr_args cdecl|.
Proof. intros H. apply Forall2_length in H. now len in H. Qed.

Lemma case_branch_context_length {ind mdecl p br cdecl} :
  wf_branch cdecl br ->
  #|case_branch_context ind mdecl p (forget_types br.(bcontext)) cdecl| = #|br.(bcontext)|.
Proof.
  intros hl.
  unfold case_branch_context, case_branch_context_gen, pre_case_branch_context_gen; len.
  rewrite map2_length //.
  * red in hl. red in hl.
    rewrite (Forall2_length hl). now len.
  * now len.
Qed.

Lemma case_branch_context_length_args {ind mdecl p br cdecl} :
  wf_branch cdecl br ->
  #|case_branch_context ind mdecl p (forget_types br.(bcontext)) cdecl| = #|cdecl.(cstr_args)|.
Proof.
  intros hl.
  unfold case_branch_context, case_branch_context_gen, pre_case_branch_context_gen; len.
  apply Forall2_length in hl.
  rewrite map2_length //. rewrite hl. now len.
Qed.

Lemma case_branch_context_assumptions {ind mdecl p br cdecl} :
  wf_branch cdecl br ->
  context_assumptions (case_branch_context ind mdecl p (forget_types br.(bcontext)) cdecl) =
  context_assumptions cdecl.(cstr_args).
Proof.
  intros hl.
  unfold case_branch_context, case_branch_context_gen, pre_case_branch_context_gen; len.
  apply Forall2_length in hl.
  rewrite /expand_lets_ctx /expand_lets_k_ctx. len.
  rewrite map2_set_binder_name_context_assumptions.
  - now rewrite hl; len.
  - len. rewrite /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx. now len.
Qed.

Lemma case_branches_contexts_length {ind mdecl idecl p pctx} :
  #|idecl.(ind_ctors)| = #|pctx| ->
  #|case_branches_contexts ind mdecl idecl p pctx| = #|pctx|.
Proof.
  intros hl.
  unfold case_branches_contexts.
  rewrite map2_length //.
Qed.

Lemma case_branch_type_length {ci mdecl idecl p br ptm i cdecl} :
  wf_branch cdecl br ->
  #|(case_branch_type ci mdecl idecl p br ptm i cdecl).1| = #|cstr_args cdecl|.
Proof.
  intros wf; simpl.
  now rewrite case_branch_context_length_args.
Qed.

Lemma lookup_inductive_declared lookup ind mdecl idecl :
  lookup_inductive_gen lookup ind = Some (mdecl, idecl) ->
  declared_inductive_gen lookup ind mdecl idecl.
Proof.
  unfold lookup_inductive_gen, lookup_minductive_gen, declared_inductive_gen,
    declared_minductive_gen.
  destruct lookup => //.
  destruct g => //.
  destruct nth_error eqn:e => //.
  intros [= -> ->]. now rewrite e.
Qed.

(** *** Helper functions for reduction/conversion *)

Fixpoint fix_subst_aux (f : nat -> term) (n : nat) : list term :=
  match n with
  | 0 => []
  | S n => f n :: fix_subst_aux f n
  end.

Definition fix_subst (l : mfixpoint term) :=
  fix_subst_aux (tFix l) (List.length l).

Definition unfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (fix_subst mfix) d.(dbody))
  | None => None
  end.

Fixpoint cofix_subst_aux (f : nat -> term) (n : nat) : list term :=
  match n with
  | 0 => []
  | S n => f n :: cofix_subst_aux f n
  end.

Definition cofix_subst (l : mfixpoint term) :=
  cofix_subst_aux (tCoFix l) (List.length l).

Definition unfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (cofix_subst mfix) d.(dbody))
  | None => None
  end.


Lemma fix_subst_length mfix : #|fix_subst mfix| = #|mfix|.
Proof.
  unfold fix_subst. generalize (tFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Lemma cofix_subst_length mfix : #|cofix_subst mfix| = #|mfix|.
Proof.
  unfold cofix_subst. generalize (tCoFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Lemma fix_context_length mfix : #|fix_context mfix| = #|mfix|.
Proof. unfold fix_context. now rewrite List.length_rev mapi_length. Qed.

#[global]
Hint Rewrite subst_instance_length
  fix_context_length fix_subst_length cofix_subst_length : len.

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a => isConstruct_app a
  | None => false
  end.

Lemma is_constructor_app_ge n l l' : is_constructor n l -> is_constructor n (l ++ l').
Proof.
  unfold is_constructor. destruct nth_error eqn:Heq => //.
  rewrite nth_error_app_lt ?Heq //; eauto using nth_error_Some_length.
Qed.

Lemma is_constructor_prefix n args args' :
  ~~ is_constructor n (args ++ args') ->
  ~~ is_constructor n args.
Proof.
  rewrite /is_constructor.
  elim: nth_error_spec.
  - rewrite length_app.
    move=> i hi harg. elim: nth_error_spec => //.
    move=> i' hi' hrarg'.
    rewrite nth_error_app_lt in hi; eauto. congruence.
  - rewrite length_app. move=> ge _.
    elim: nth_error_spec; intros; try lia. auto.
Qed.

