(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import CMorphisms.
From MetaRocq.Utils Require Import LibHypsNaming utils.
From MetaRocq.Common Require Import config Reflect.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICReflect.

From Stdlib Require Import ssreflect ssrbool.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

Ltac pcuic :=
  try repeat red; cbn in *;
   try (solve [ intuition auto; eauto with pcuic || (try lia || congruence) ]).

#[global]
Instance All2_fold_len {A} P (Γ Δ : list A) : HasLen (All2_fold P Γ Δ) #|Γ| #|Δ| :=
  All2_fold_length.

Implicit Types (cf : checker_flags).

Definition cmp_universe_instance (cmp_univ : Universe.t -> Universe.t -> Prop) : Instance.t -> Instance.t -> Prop :=
  Forall2 cmp_univ.

Definition cmp_universe_instance_dep cmp_univ P' :=
  fun {u u'} (H : cmp_universe_instance cmp_univ u u') => Forall2_dep P' H.

(** Cumulative inductive types:

  To simplify the development, we allow the variance list to not exactly
  match the instances, so as to keep syntactic ws_cumul_pb an equivalence relation
  even on ill-formed terms. It corresponds to the right notion on well-formed terms.
*)

Definition cmp_universe_variance (cmp_univ : conv_pb -> Universe.t -> Universe.t -> Prop) pb v u u' :=
  match v with
  | Variance.Irrelevant => True
  | Variance.Covariant => cmp_univ pb u u'
  | Variance.Invariant => cmp_univ Conv u u'
  end.

Definition cmp_universe_instance_variance cmp_univ pb v u u' :=
  Forall3 (cmp_universe_variance cmp_univ pb) v u u'.

Definition global_variance_gen lookup gr napp :=
  match gr with
  | IndRef ind =>
    match lookup_inductive_gen lookup ind with
    | Some (mdecl, idecl) =>
      match destArity [] idecl.(ind_type) with
      | Some (ctx, _) => if (context_assumptions ctx) <=? napp then
          match mdecl.(ind_variance) with
          | Some var => Variance var
          | None => AllEqual
          end
        else AllEqual
      | None => AllEqual
      end
    | None => AllEqual
    end
  | ConstructRef ind k =>
    match lookup_constructor_gen lookup ind k with
    | Some (mdecl, idecl, cdecl) =>
      if (cdecl.(cstr_arity) + mdecl.(ind_npars))%nat <=? napp then
        (** Fully applied constructors are always compared at the same supertype,
          which implies that no universe ws_cumul_pb needs to be checked here.
          We will still check that the instances have the same length. *)
        AllIrrelevant
      else AllEqual
    | _ => AllEqual
    end
  | _ => AllEqual
  end.

Notation global_variance Σ := (global_variance_gen (lookup_env Σ)).

Definition cmp_opt_variance cmp_univ pb v :=
  match v with
  | AllEqual => cmp_universe_instance (cmp_univ Conv)
  | AllIrrelevant => fun l l' => #|l| = #|l'|
  | Variance v => fun u u' => cmp_universe_instance (cmp_univ Conv) u u' \/ cmp_universe_instance_variance cmp_univ pb v u u'
  end.

Lemma cmp_universe_universe_variance (cmp_univ : conv_pb -> Universe.t -> Universe.t -> Prop) pb v u u' :
  RelationClasses.subrelation (cmp_univ Conv) (cmp_univ pb) ->
  cmp_univ Conv u u' -> cmp_universe_variance cmp_univ pb v u u'.
Proof.
  destruct v => //=.
  intros H H1; apply H, H1.
Qed.

Lemma cmp_instance_variance cmp_univ pb v u u' :
  RelationClasses.subrelation (cmp_univ Conv) (cmp_univ pb) ->
  #|v| = #|u| ->
  cmp_universe_instance (cmp_univ Conv) u u' -> cmp_universe_instance_variance cmp_univ pb v u u'.
Proof.
  intros Hsub Hlen Hu.
  apply Forall2_triv in Hlen.
  eapply Forall2_Forall2_Forall3 in Hu; tea.
  apply Forall3_impl with (1 := Hu) => v1 u1 u1' [] _ H1.
  now apply cmp_universe_universe_variance.
Qed.

Lemma cmp_instance_opt_variance cmp_univ pb v :
  RelationClasses.subrelation (cmp_opt_variance cmp_univ pb AllEqual) (cmp_opt_variance cmp_univ pb v).
Proof.
  intros u u' H.
  destruct v as [| |v] => //=.
  1: now apply Forall2_length in H.
  now left.
Qed.

Lemma cmp_opt_variance_var_dec cmp_univ pb v ui ui' :
  RelationClasses.subrelation (cmp_univ Conv) (cmp_univ pb) ->
  cmp_universe_instance (cmp_univ Conv) ui ui' \/ cmp_universe_instance_variance cmp_univ pb v ui ui' ->
  { cmp_universe_instance (cmp_univ Conv) ui ui' } + { cmp_universe_instance_variance cmp_univ pb v ui ui' }.
Proof.
  intros subr H.
  elim:(eq_dec #|v| #|ui|).
  - right.
    destruct H as [|]; tas.
    now eapply cmp_instance_variance.
  - left.
    destruct H as [|]; tas.
    eapply @Forall3_Forall2_left with (Q := fun _ _ => True) in H => //.
    apply Forall2_length in H.
    now exfalso.
Qed.

Lemma cmp_opt_variance_length cmp_univ pb v ui ui' :
  cmp_opt_variance cmp_univ pb v ui ui' -> #|ui| = #|ui'|.
Proof.
  destruct v => //=.
  1: apply Forall2_length.
  move => [|].
  1: apply Forall2_length.
  intro H.
  eapply @Forall2_length with (P := fun _ _ => True).
  now eapply Forall3_Forall2_right => //.
Qed.

Lemma cmp_opt_variance_or_impl cmp_universe1 cmp_universe2 cmp_universe3 pb1 pb2 pb3 v u1 u1' u2 u2' u3 u3' :
  RelationClasses.subrelation (cmp_universe1 Conv) (cmp_universe1 pb1) ->
  RelationClasses.subrelation (cmp_universe2 Conv) (cmp_universe2 pb2) ->
  (cmp_universe_instance (cmp_universe1 Conv) u1 u1' -> cmp_universe_instance (cmp_universe2 Conv) u2 u2' -> cmp_universe_instance (cmp_universe3 Conv) u3 u3') ->
  (cmp_universe_instance_variance cmp_universe1 pb1 v u1 u1' -> cmp_universe_instance_variance cmp_universe2 pb2 v u2 u2' -> cmp_universe_instance_variance cmp_universe3 pb3 v u3 u3') ->
  (#|u1| = #|u1'| -> #|u2| = #|u2'| -> #|u1| = #|u2|) ->
  cmp_universe_instance (cmp_universe1 Conv) u1 u1' \/ cmp_universe_instance_variance cmp_universe1 pb1 v u1 u1' ->
  cmp_universe_instance (cmp_universe2 Conv) u2 u2' \/ cmp_universe_instance_variance cmp_universe2 pb2 v u2 u2' ->
  cmp_universe_instance (cmp_universe3 Conv) u3 u3' \/ cmp_universe_instance_variance cmp_universe3 pb3 v u3 u3'.
Proof.
  intros Hsub1 Hsub2 Hl Hr e [H|H] [H'|H']; [left; apply Hl| right; apply Hr ..]; auto.
  all: apply cmp_instance_variance; tas.
  - rewrite e.
    all: eapply Forall2_length; tea.
    + eapply @Forall3_Forall2_right with (Q := fun _ _ => True); eauto.
    + eapply @Forall3_Forall2_left with (Q := fun _ _ => True); eauto.
  - rewrite -e.
    all: eapply Forall2_length; tea.
    + eapply @Forall3_Forall2_right with (Q := fun _ _ => True); eauto.
    + eapply @Forall3_Forall2_left with (Q := fun _ _ => True); eauto.
Qed.

Definition cmp_global_instance_gen Σ cmp_universe pb gr napp :=
  cmp_opt_variance cmp_universe pb (global_variance_gen Σ gr napp).

Notation cmp_global_instance Σ := (cmp_global_instance_gen (lookup_env Σ)).

Definition cmp_ind_universes {cf:checker_flags} (Σ : global_env_ext) ind n i i' :=
  cmp_global_instance Σ (compare_universe (global_ext_constraints Σ)) Cumul (IndRef ind) n i i'.

Lemma cmp_universe_instance_impl R R' :
  RelationClasses.subrelation R R' ->
  RelationClasses.subrelation (cmp_universe_instance R) (cmp_universe_instance R').
Proof.
  intros H x y xy. eapply Forall2_impl; tea; unfold on_rel; auto.
Qed.

Lemma cmp_universe_instance_impl' R R' :
  RelationClasses.subrelation R R' ->
  forall u u', cmp_universe_instance R u u' -> cmp_universe_instance R' u u'.
Proof.
  intros H x y xy. eapply Forall2_impl; tea; unfold on_rel; auto.
Qed.

Lemma cmp_universe_variance_impl R R' pb pb' v :
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R pb) (R' pb') ->
  RelationClasses.subrelation (cmp_universe_variance R pb v) (cmp_universe_variance R' pb' v).
Proof.
  intros HConv Hpb x y.
  destruct v => //=.
  all: unfold on_rel; now auto.
Qed.

Lemma cmp_universe_instance_variance_impl R R' pb pb' v :
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R pb) (R' pb') ->
  RelationClasses.subrelation (cmp_universe_instance_variance R pb v) (cmp_universe_instance_variance R' pb' v).
Proof.
  intros HConv Hpb x y xy.
  eapply Forall3_impl; tea.
  intros ???.
  now apply cmp_universe_variance_impl.
Qed.

Inductive eq_decl_upto_names : context_decl -> context_decl -> Type :=
  | compare_vass {na na' T} :
    eq_binder_annot na na' -> eq_decl_upto_names (vass na T) (vass na' T)
  | compare_vdef {na na' b T} :
    eq_binder_annot na na' -> eq_decl_upto_names (vdef na b T) (vdef na' b T).
Derive Signature NoConfusion for eq_decl_upto_names.
#[global] Hint Constructors eq_decl_upto_names : pcuic.

Definition compare_decls cmp_term pb := PCUICConversion.All_decls_alpha_pb pb cmp_term.

Notation eq_context_upto_names := (All2 eq_decl_upto_names).

Notation eq_context_gen cmp_term pb :=
  (All2_fold (fun _ _ => compare_decls cmp_term pb)).

Lemma eq_decl_upto_names_gen decl decl' pb : eq_decl_upto_names decl decl' <~> compare_decls (fun _ => eq) pb decl decl'.
Proof.
  split; intros e; depind e; subst; constructor; auto.
Qed.

Lemma eq_context_upto_names_gen Γ Γ' pb : eq_context_upto_names Γ Γ' <~> eq_context_gen (fun _ => eq) pb Γ Γ'.
Proof.
  split; intros e; depind e; constructor; tas; now eapply eq_decl_upto_names_gen.
Qed.

Lemma compare_decls_impl cmp_term cmp_term' pb pb' :
  subrelation (cmp_term Conv) (cmp_term' Conv) ->
  subrelation (cmp_term pb) (cmp_term' pb') ->
  subrelation (compare_decls cmp_term pb) (compare_decls cmp_term' pb').
Proof.
  intros he hle x y []; constructor; auto.
Qed.

Lemma eq_context_gen_impl cmp_term cmp_term' pb pb' :
  subrelation (cmp_term Conv) (cmp_term' Conv) ->
  subrelation (cmp_term pb) (cmp_term' pb') ->
  subrelation (eq_context_gen cmp_term pb) (eq_context_gen cmp_term' pb').
Proof.
  intros he hle x y eq.
  eapply All2_fold_impl; tea => /=.
  intros; eapply compare_decls_impl; tea.
Qed.

Lemma compare_decl_impl_ondecl P cmp_term cmp_term' pb pb' d d' :
  ondecl P d ->
  (forall x y, P x -> cmp_term Conv x y -> cmp_term' Conv x y) ->
  (forall x y, P x -> cmp_term pb x y -> cmp_term' pb' x y) ->
  compare_decls cmp_term pb d d' ->
  compare_decls cmp_term' pb' d d'.
Proof.
  intros ond he hle cd; depelim cd; depelim ond; constructor => //; eauto.
Qed.

Lemma compare_decl_map cmp_term pb f g d d' :
  compare_decls (fun pb x y => cmp_term pb (f x) (g y)) pb d d' ->
  compare_decls cmp_term pb (map_decl f d) (map_decl g d').
Proof.
  intros h; depelim h; constructor; intuition auto.
Qed.

#[global]
Polymorphic Instance compare_decl_refl cmp_term pb :
  CRelationClasses.Reflexive (cmp_term Conv) ->
  CRelationClasses.Reflexive (cmp_term pb) ->
  CRelationClasses.Reflexive (compare_decls cmp_term pb).
Proof.
  intros heq hle d.
  destruct d as [na [b|] ty]; constructor; auto; reflexivity.
Qed.

#[global]
Polymorphic Instance compare_decl_sym cmp_term pb :
  CRelationClasses.Symmetric (cmp_term Conv) ->
  CRelationClasses.Symmetric (cmp_term pb) ->
  CRelationClasses.Symmetric (compare_decls cmp_term pb).
Proof.
  intros heq hle d d' []; constructor; auto; now symmetry.
Qed.

#[global]
Polymorphic Instance compare_decl_trans cmp_term pb :
  CRelationClasses.Transitive (cmp_term Conv) ->
  CRelationClasses.Transitive (cmp_term pb) ->
  CRelationClasses.Transitive (compare_decls cmp_term pb).
Proof.
  intros hle hre x y z h h'; depelim h; depelim h'; constructor; auto;
  etransitivity; eauto.
Qed.

#[global]
Polymorphic Instance eq_decl_upto_names_refl :
  CRelationClasses.Reflexive eq_decl_upto_names.
Proof.
  intros d.
  destruct d as [na [b|] ty]; constructor; auto; reflexivity.
Qed.

#[global]
Polymorphic Instance eq_decl_upto_names_sym :
  CRelationClasses.Symmetric eq_decl_upto_names.
Proof.
  intros d d' []; constructor; auto; now symmetry.
Qed.

#[global]
Polymorphic Instance eq_decl_upto_names_trans :
  CRelationClasses.Transitive eq_decl_upto_names.
Proof.
  intros x y z h h'; depelim h; depelim h'; constructor; auto;
  etransitivity; eauto.
Qed.

#[global]
Instance alpha_eq_reflexive : CRelationClasses.Reflexive eq_context_upto_names.
Proof.
  intros x. eapply All2_refl. reflexivity.
Qed.

#[global]
Instance alpha_eq_symmmetric : CRelationClasses.Symmetric eq_context_upto_names.
Proof.
  intros x. eapply All2_symP. tc.
Qed.

#[global]
Instance alpha_eq_trans : CRelationClasses.Transitive eq_context_upto_names.
Proof.
  intros x y z. apply All2_trans. tc.
Qed.

#[global]
Polymorphic Instance eq_context_refl cmp_term pb :
  CRelationClasses.Reflexive (cmp_term Conv) ->
  CRelationClasses.Reflexive (cmp_term pb) ->
  CRelationClasses.Reflexive (eq_context_gen cmp_term pb).
Proof.
  intros heq hle x.
  eapply All2_fold_refl.
  intros. reflexivity.
Qed.

#[global]
Polymorphic Instance eq_context_sym cmp_term pb :
  CRelationClasses.Symmetric (cmp_term Conv) ->
  CRelationClasses.Symmetric (cmp_term pb) ->
  CRelationClasses.Symmetric (eq_context_gen cmp_term pb).
Proof.
  intros heq hle x.
  eapply All2_fold_sym.
  intros. now symmetry.
Qed.

#[global]
Polymorphic Instance eq_context_trans cmp_term pb :
  CRelationClasses.Transitive (cmp_term Conv) ->
  CRelationClasses.Transitive (cmp_term pb) ->
  CRelationClasses.Transitive (eq_context_gen cmp_term pb).
Proof.
  intros hr x y z.
  eapply All2_fold_trans; intros.
  now transitivity y0.
Qed.

Definition eq_predicate (eq_term : term -> term -> Type) eq_universe p p' :=
  All2 eq_term p.(pparams) p'.(pparams) ×
  cmp_universe_instance eq_universe p.(puinst) p'.(puinst) ×
  eq_context_upto_names p.(pcontext) p'.(pcontext) ×
  eq_term p.(preturn) p'.(preturn).

Definition eq_branch (eq_term : term -> term -> Type) br br' :=
  eq_context_upto_names br.(bcontext) br'.(bcontext) ×
  eq_term br.(bbody) br'.(bbody).

Definition eq_branches eq_term brs brs' := All2 (eq_branch eq_term) brs brs'.

Definition eq_mfixpoint (eq_term : term -> term -> Type) mfix mfix' :=
  All2 (fun d d' =>
    eq_term d.(dtype) d'.(dtype) ×
    eq_term d.(dbody) d'.(dbody) ×
    d.(rarg) = d'.(rarg) ×
    eq_binder_annot d.(dname) d'.(dname)
  ) mfix mfix'.


(** ** Syntactic ws_cumul_pb up-to universes
  We don't look at printing annotations *)

(** ws_cumul_pb is indexed by a natural number that counts the number of applications
  that surround the current term, used to implement cumulativity of inductive types
  correctly (only fully applied constructors and inductives benefit from it). *)

Reserved Notation " Σ ⊢ t <==[ Rle , napp ] u" (at level 50, t, u at next level,
  format "Σ  ⊢  t  <==[ Rle , napp ]  u").

Inductive eq_term_upto_univ_napp Σ
  (cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop)
  (cmp_sort : conv_pb -> sort -> sort -> Prop)
  (pb : conv_pb) (napp : nat) : term -> term -> Type :=
| eq_Rel : forall n,
    Σ ⊢ tRel n <==[ pb , napp ] tRel n

| eq_Evar : forall e args args',
    All2 (fun arg arg' => (Σ ⊢ arg <==[ Conv , 0 ] arg')) args args' ->
    Σ ⊢ tEvar e args <==[ pb , napp ] tEvar e args'

| eq_Var : forall id,
    Σ ⊢ tVar id <==[ pb , napp ] tVar id

| eq_Sort : forall s s',
    cmp_sort pb s s' ->
    Σ ⊢ tSort s  <==[ pb , napp ] tSort s'

| eq_App : forall t t' u u',
    Σ ⊢ t <==[ pb , S napp ] t' ->
    Σ ⊢ u <==[ Conv , 0 ] u' ->
    Σ ⊢ tApp t u <==[ pb , napp ] tApp t' u'

| eq_Const : forall c u u',
    cmp_universe_instance (cmp_universe Conv) u u' ->
    Σ ⊢ tConst c u <==[ pb , napp ] tConst c u'

| eq_Ind : forall i u u',
    cmp_global_instance Σ cmp_universe pb (IndRef i) napp u u' ->
    Σ ⊢ tInd i u <==[ pb , napp ] tInd i u'

| eq_Construct : forall i k u u',
    cmp_global_instance Σ cmp_universe pb (ConstructRef i k) napp u u' ->
    Σ ⊢ tConstruct i k u <==[ pb , napp ] tConstruct i k u'

| eq_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ⊢ ty <==[ Conv , 0 ] ty' ->
    Σ ⊢ t <==[ Conv , 0 ] t' ->
    Σ ⊢ tLambda na ty t <==[ pb , napp ] tLambda na' ty' t'

| eq_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ⊢ a <==[ Conv , 0 ] a' ->
    Σ ⊢ b <==[ pb , 0 ] b' ->
    Σ ⊢ tProd na a b <==[ pb , napp ] tProd na' a' b'

| eq_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ⊢ t <==[ Conv , 0 ] t' ->
    Σ ⊢ ty <==[ Conv , 0 ] ty' ->
    Σ ⊢ u <==[ Conv , 0 ] u' ->
    Σ ⊢ tLetIn na t ty u <==[ pb , napp ] tLetIn na' t' ty' u'

| eq_Case : forall indn p p' c c' brs brs',
    eq_predicate (fun t t' => Σ ⊢ t <==[ Conv , 0 ] t') (cmp_universe Conv) p p' ->
    Σ ⊢ c <==[ Conv , 0 ] c' ->
    eq_branches (fun t t' => Σ ⊢ t <==[ Conv , 0 ] t') brs brs' ->
    Σ ⊢ tCase indn p c brs <==[ pb , napp ] tCase indn p' c' brs'

| eq_Proj : forall p c c',
    Σ ⊢ c <==[ Conv , 0 ] c' ->
    Σ ⊢ tProj p c <==[ pb , napp ] tProj p c'

| eq_Fix : forall mfix mfix' idx,
    eq_mfixpoint (fun t t' => Σ ⊢ t <==[ Conv , 0 ] t') mfix mfix' ->
    Σ ⊢ tFix mfix idx <==[ pb , napp ] tFix mfix' idx

| eq_CoFix : forall mfix mfix' idx,
    eq_mfixpoint (fun t t' => Σ ⊢ t <==[ Conv , 0 ] t') mfix mfix' ->
    Σ ⊢ tCoFix mfix idx <==[ pb , napp ] tCoFix mfix' idx

| eq_Prim i i' :
    onPrims (fun t t' => Σ ⊢ t <==[ Conv , 0 ] t') (cmp_universe Conv) i i' ->
    Σ ⊢ tPrim i <==[ pb , napp ] tPrim i'
where " Σ ⊢ t <==[ pb , napp ] u " := (eq_term_upto_univ_napp Σ _ _ pb napp t u) : type_scope.

Notation eq_term_upto_univ Σ cmp_universe cmp_sort pb := (eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb 0) (only parsing).

(* ** Syntactic conparison up-to universes *)

Definition compare_term_napp `{checker_flags} Σ φ (pb : conv_pb) napp (t u : term) :=
  eq_term_upto_univ_napp Σ (compare_universe φ) (compare_sort φ) pb napp t u.

Definition compare_term `{checker_flags} Σ φ (pb : conv_pb) (t u : term) :=
  eq_term_upto_univ Σ (compare_universe φ) (compare_sort φ) pb t u.

(* ** Syntactic conversion up-to universes *)

Notation eq_term Σ φ := (compare_term Σ φ Conv).

(* ** Syntactic cumulativity up-to universes *)

Notation leq_term Σ φ := (compare_term Σ φ Cumul).

Definition compare_opt_term `{checker_flags} (pb : conv_pb) Σ φ (t u : option term) :=
  match t, u with
  | Some t, Some u => compare_term Σ φ pb t u
  | None, None => True
  | _, _ => False
  end.

Definition compare_decl `{checker_flags} Σ φ pb (d d' : context_decl) :=
  compare_decls (compare_term Σ φ) pb d d'.

Notation eq_decl Σ φ := (compare_decl Σ φ Conv).
Notation leq_decl Σ φ := (compare_decl Σ φ Cumul).

Definition compare_context `{checker_flags} Σ φ pb (Γ Δ : context) :=
  eq_context_gen (compare_term Σ φ) pb Γ Δ.

Notation eq_context Σ φ := (compare_context Σ φ Conv).
Notation leq_context Σ φ := (compare_context Σ φ Cumul).

Notation eq_context_upto Σ cmp_universe cmp_sort pb :=
  (eq_context_gen (fun pb0 => eq_term_upto_univ Σ cmp_universe cmp_sort pb0) pb).

(* TODO MOVE *)
#[global]
Existing Instance All2_symP.

(* TODO MOVE *)
#[global]
Existing Instance Forall2_symP.

#[global]
Instance cmp_universe_instance_refl cmp_universe :
  RelationClasses.Reflexive cmp_universe ->
  RelationClasses.Reflexive (cmp_universe_instance cmp_universe).
Proof.
  intros refl_univ u.
  apply Forall2_same; reflexivity.
Qed.

#[global]
Instance cmp_universe_instance_sym cmp_universe :
  RelationClasses.Symmetric cmp_universe ->
  RelationClasses.Symmetric (cmp_universe_instance cmp_universe).
Proof. intros tRe x y. now eapply Forall2_symP. Qed.

#[global]
Instance cmp_universe_instance_trans cmp_universe :
  RelationClasses.Transitive cmp_universe ->
  RelationClasses.Transitive (cmp_universe_instance cmp_universe).
Proof. intros tRe x y z. eapply Forall2_trans. tc. Qed.

#[global]
Instance cmp_universe_variance_sym cmp_universe pb v :
  RelationClasses.Symmetric (cmp_universe Conv) ->
  RelationClasses.Symmetric (cmp_universe pb) ->
  RelationClasses.Symmetric (cmp_universe_variance cmp_universe pb v).
Proof.
  intros univ_sym univ_sym' u u' u''.
  destruct v as [| |] => //=.
  all: now symmetry.
Qed.

#[global]
Instance cmp_universe_variance_trans cmp_universe pb v :
  RelationClasses.Transitive (cmp_universe Conv) ->
  RelationClasses.Transitive (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_universe_variance cmp_universe pb v).
Proof.
  intros univ_trans univ_trans' u u' u''.
  destruct v as [| |] => //=.
  all: now etransitivity.
Qed.

#[global]
Instance cmp_universe_instance_variance_sym cmp_universe pb v :
  RelationClasses.Symmetric (cmp_universe Conv) ->
  RelationClasses.Symmetric (cmp_universe pb) ->
  RelationClasses.Symmetric (cmp_universe_instance_variance cmp_universe pb v).
Proof.
  intros univ_sym univ_sym' u u'.
  apply Forall3_symP. tc.
Qed.

#[global]
Instance cmp_universe_instance_variance_trans cmp_universe pb v :
  RelationClasses.Transitive (cmp_universe Conv) ->
  RelationClasses.Transitive (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_universe_instance_variance cmp_universe pb v).
Proof.
  intros univ_trans univ_trans' u u' u''.
  apply Forall3_transP. tc.
Qed.

#[global]
Instance cmp_global_instance_refl Σ cmp_universe pb gr napp :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_global_instance Σ cmp_universe pb gr napp).
Proof.
  intros rRE rRle.
  unfold cmp_global_instance_gen.
  destruct global_variance_gen as [| |v] => //= u.
  - now apply cmp_universe_instance_refl.
  - left. now apply cmp_universe_instance_refl.
Qed.

#[global]
Instance cmp_global_instance_sym Σ cmp_universe pb gr napp :
  RelationClasses.Symmetric (cmp_universe Conv) ->
  RelationClasses.Symmetric (cmp_universe pb) ->
  RelationClasses.Symmetric (cmp_global_instance Σ cmp_universe pb gr napp).
Proof.
  intros univ_sym univ_sym'.
  unfold cmp_global_instance_gen.
  destruct global_variance_gen as [| |v] => //= u u'.
  - now symmetry.
  - intros [H | H]; [left|right].
    all: now symmetry.
Qed.

#[global]
Instance cmp_global_instance_trans Σ cmp_universe pb gr napp :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_universe Conv) ->
  RelationClasses.Transitive (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_global_instance Σ cmp_universe pb gr napp).
Proof.
  intros univ_sub univ_trans univ_trans'.
  unfold cmp_global_instance_gen.
  destruct global_variance_gen as [| |v] => //= u u' u''.
  1,2: now etransitivity.

  apply cmp_opt_variance_or_impl; tas.
  all: now etransitivity.
Qed.

#[global]
Instance eq_binder_annot_equiv {A} : RelationClasses.Equivalence (@eq_binder_annot A A).
Proof.
  split.
  - red. reflexivity.
  - red; now symmetry.
  - intros x y z; unfold eq_binder_annot.
    apply transitivity.
Qed.

Definition eq_binder_annot_refl {A} x : @eq_binder_annot A A x x.
Proof. reflexivity. Qed.

#[global]
Hint Resolve eq_binder_annot_refl : core.


Lemma eq_binder_relevances_refl (x : list aname) : All2 (on_rel eq binder_relevance) x x.
Proof. now eapply All_All2_refl, All_refl. Qed.
#[global]
Hint Resolve eq_binder_relevances_refl : core.

Lemma onctx_eq_ctx P ctx cmp_term pb :
  onctx P ctx ->
  (forall x, P x -> cmp_term Conv x x) ->
  (forall x, P x -> cmp_term pb x x) ->
  eq_context_gen cmp_term pb ctx ctx.
Proof.
  intros onc HP HP'.
  induction onc.
  - constructor; auto.
  - constructor; auto; simpl.
    destruct x as [na [b|] ty]; destruct p; simpl in *;
    constructor; auto.
Qed.

#[global]
Polymorphic Instance creflexive_eq A : CRelationClasses.Reflexive (@eq A).
Proof. intro x. constructor. Qed.

#[global]
Polymorphic Instance eq_predicate_refl Re Ru :
  CRelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Ru ->
  CRelationClasses.Reflexive (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p. unfold eq_predicate; intuition auto; try reflexivity.
  eapply All2_same; reflexivity.
Qed.

#[global]
Polymorphic Instance eq_branches_refl Re :
  CRelationClasses.Reflexive Re ->
  CRelationClasses.Reflexive (eq_branches Re).
Proof.
  intros hre.
  intros brs. unfold eq_branches, eq_branch.
  apply All2_same. intuition auto; try reflexivity.
Qed.

#[global]
Polymorphic Instance eq_mfixpoint_refl Re :
  CRelationClasses.Reflexive Re ->
  CRelationClasses.Reflexive (eq_mfixpoint Re).
Proof.
  intros hre.
  intros mfix.
  apply All2_same. intuition auto; try reflexivity.
Qed.


#[global]
Polymorphic Instance eq_term_upto_univ_refl Σ cmp_universe cmp_sort pb napp :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  Reflexive (eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp).
Proof.
  intros refl_univ refl_univ' refl_sort refl_sort' t.
  induction t in napp, pb, refl_univ', refl_sort' |- * using term_forall_list_ind.
  all: simpl.
  all: try constructor. all: eauto.
  all: try reflexivity.
  all: try solve [eapply All_All2 ; eauto].
  - unfold eq_predicate. solve_all.
    2,3: reflexivity.
    eapply All_All2; eauto.
  - unfold eq_branches, eq_branch.
    eapply All_All2; eauto.
    intros br [_ ?]; split; eauto. reflexivity.
  - eapply All_All2; eauto; simpl; intuition eauto.
  - eapply All_All2; eauto; simpl; intuition eauto.
  - destruct p as [? []]; constructor; cbn in X; intuition eauto.
    eapply All_All2; eauto.
Qed.

#[global]
Polymorphic Instance All2_eq_refl Σ cmp_universe cmp_sort :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  CRelationClasses.Reflexive (All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv)).
Proof using Type.
  intros h h' x. apply All2_same. reflexivity.
Qed.

#[global]
Instance compare_term_refl {cf} pb {Σ : global_env} φ : Reflexive (compare_term Σ φ pb).
Proof. eapply eq_term_upto_univ_refl; tc. Qed.

Derive Signature for eq_term_upto_univ_napp.

Lemma onctx_eq_ctx_sym P ctx ctx' cmp_term pb :
  onctx P ctx ->
  (forall x, P x -> forall y, cmp_term Conv x y -> cmp_term Conv y x) ->
  (forall x, P x -> forall y, cmp_term pb x y -> cmp_term pb y x) ->
  eq_context_gen cmp_term pb ctx ctx' ->
  eq_context_gen cmp_term pb ctx' ctx.
Proof.
  intros onc HP HP' H1.
  induction H1; depelim onc; constructor; intuition auto; simpl in *.
  destruct p; depelim o; constructor; eauto; now symmetry.
Qed.

#[global]
Polymorphic Instance eq_term_upto_univ_sym Σ cmp_universe cmp_sort pb napp :
  RelationClasses.Symmetric (cmp_universe Conv) ->
  RelationClasses.Symmetric (cmp_universe pb) ->
  RelationClasses.Symmetric (cmp_sort Conv) ->
  RelationClasses.Symmetric (cmp_sort pb) ->
  Symmetric (eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp).
Proof.
  intros sym_univ sym_univ' sym_sort sym_sort' u v e.
  pose proof (@RelationClasses.symmetry _ (@eq_binder_annot name name) _).
  induction u in napp, pb, sym_univ', sym_sort', v, e |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try solve [
    econstructor ; eauto ;
    try eapply Forall2_symP ; eauto ; easy
  ].
  - econstructor.
    apply All2_sym. solve_all.
  - solve_all. destruct e as (r & ? & eq & ?).
    econstructor; rewrite ?e; unfold eq_predicate, eq_branches, eq_branch in *; repeat split; eauto.
    2,3: now symmetry.
    all: eapply All2_sym; solve_all.
    apply All2_symP; solve_all. tc.
  - econstructor. unfold eq_mfixpoint in *.
    apply All2_sym. solve_all.
  - econstructor. unfold eq_mfixpoint in *.
    apply All2_sym. solve_all.
  - econstructor.
    depelim o; cbn in X; constructor; intuition eauto.
    eapply All2_All_mix_left in a0 as h; eauto. cbn in h.
    eapply All2_sym; solve_all.
Qed.

#[global]
Polymorphic Instance eq_predicate_sym Re Ru :
  CRelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Ru ->
  CRelationClasses.Symmetric (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p. unfold eq_predicate; intuition auto; try now symmetry.
Qed.

#[global]
Instance compare_term_sym {cf} Σ φ : Symmetric (compare_term Σ φ Conv).
Proof.
  now intros t u; unfold compare_term; cbn; symmetry.
Qed.

Lemma onctx_eq_ctx_trans P ctx ctx' ctx'' cmp_term pb :
  onctx P ctx ->
  (forall x, P x -> forall y z, cmp_term Conv x y -> cmp_term Conv y z -> cmp_term Conv x z) ->
  (forall x, P x -> forall y z, cmp_term pb x y -> cmp_term pb y z -> cmp_term pb x z) ->
  eq_context_gen cmp_term pb ctx ctx' ->
  eq_context_gen cmp_term pb ctx' ctx'' ->
  eq_context_gen cmp_term pb ctx ctx''.
Proof.
  intros onc HP  HP' H1; revert ctx''.
  induction H1; depelim onc; intros ctx'' H; depelim H; constructor; intuition auto; simpl in *.
  depelim o. depelim p0.
  - depelim c; constructor; [now etransitivity|eauto].
  - depelim c; constructor; [now etransitivity|eauto ..].
Qed.

#[global]
Polymorphic Instance eq_predicate_trans Re Ru :
  CRelationClasses.Transitive Re ->
  RelationClasses.Transitive Ru ->
  CRelationClasses.Transitive (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p. unfold eq_predicate; intuition auto; try now etransitivity.
  eapply All2_trans; tea.
  etransitivity; tea.
Qed.

#[global]
Polymorphic Instance eq_term_upto_univ_trans Σ cmp_universe cmp_sort pb napp :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_universe Conv) ->
  RelationClasses.Transitive (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_sort Conv) ->
  RelationClasses.Transitive (cmp_sort pb) ->
  Transitive (eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp).
Proof.
  intros sub_univ trans_univ trans_univ' trans_sort trans_sort' u v w e1 e2.
  pose proof (@RelationClasses.transitivity _ (@eq_binder_annot name name) _).
  assert (RelationClasses.subrelation (cmp_universe Conv) (cmp_universe Conv)) by reflexivity.
  induction u in napp, pb, sub_univ, trans_univ', trans_sort', v, w, e1, e2 |- * using term_forall_list_ind.
  all: dependent destruction e1.
  all: try solve [ eauto ].
  all: try solve [
    dependent destruction e2 ; econstructor ; eauto ;
    try now etransitivity
  ].
  - dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    eapply All2_trans'; tea.
    intros u v w [[IH]]. now eapply IH.
  - dependent destruction e2.
    unfold eq_predicate, eq_branches, eq_branch in *.
    !!solve_all.
    econstructor; unfold eq_predicate, eq_branches, eq_branch in *; solve_all; eauto.
    2: now etransitivity.
    all: eapply All2_trans'; tea; intros ??? [[IH]]; repeat split; eauto.
    * etransitivity; eassumption.
    * destruct p0, p1; etransitivity; eassumption.
    * destruct IH, p0, p1; eauto.
  - dependent destruction e2.
    econstructor. unfold eq_mfixpoint in *.
    eapply All2_All_mix_left in X as h; eauto.
    eapply All2_trans'; tea.
    intros u v w [[[IHt IHb] (?&?&?&?)] (?&?&?&?)]. repeat split; eauto. now etransitivity.
  - dependent destruction e2.
    econstructor. unfold eq_mfixpoint in *.
    eapply All2_All_mix_left in X as h; eauto.
    eapply All2_trans'; tea.
    intros u v w [[[IHt IHb] (?&?&?&?)] (?&?&?&?)]. repeat split; eauto. now etransitivity.
  - dependent destruction e2; constructor.
    depelim o; tas. depelim o0. constructor; destruct X as (hty & hdef & harr); eauto.
    eapply All2_All_mix_left in harr as h; eauto.
    eapply All2_trans'; tea.
    intros ??? [[IH]]; repeat split; eauto.
Qed.

#[global]
Instance compare_term_trans {cf} pb Σ φ : Transitive (compare_term Σ φ pb).
Proof. apply eq_term_upto_univ_trans; tc. Qed.

#[global]
Polymorphic Instance eq_term_upto_univ_equiv Σ cmp_universe cmp_sort :
  RelationClasses.Equivalence (cmp_universe Conv) ->
  RelationClasses.Equivalence (cmp_sort Conv) ->
  Equivalence (eq_term_upto_univ Σ cmp_universe cmp_sort Conv).
Proof.
  constructor. all: exact _.
Defined.

#[global]
Polymorphic Instance eq_context_equiv {cf} Σ φ : Equivalence (eq_context_gen (compare_term Σ φ) Conv).
Proof.
  constructor; try exact _.
Qed.

#[global]
Polymorphic Instance leq_context_preord {cf} Σ φ : PreOrder (eq_context_gen (compare_term Σ φ) Cumul).
Proof.
  constructor; try exact _.
Qed.

#[global]
Polymorphic Instance eq_term_equiv {cf:checker_flags} Σ φ : Equivalence (eq_term Σ φ).
Proof. split; tc. Qed.

#[global]
Polymorphic Instance leq_term_preorder {cf:checker_flags} Σ φ : PreOrder (leq_term Σ φ).
Proof. split; tc. Qed.

#[global]
Instance cmp_universe_instance_equiv R (hR : RelationClasses.Equivalence R)
  : RelationClasses.Equivalence (cmp_universe_instance R).
Proof.
  split.
  - intro. apply Forall2_same. reflexivity.
  - intros x y xy. eapply Forall2_sym, Forall2_impl; tea. now symmetry.
  - intros x y z xy yz. eapply Forall2_trans; tea. apply on_rel_trans. apply hR.
Qed.

Lemma cmp_universe_instance_antisym cmp_universe pb (hE : RelationClasses.Equivalence (cmp_universe Conv)) :
  RelationClasses.Antisymmetric _ (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Antisymmetric _ (cmp_universe_instance (cmp_universe Conv)) (cmp_universe_instance (cmp_universe pb)).
Proof.
  intros H x y H1 H2.
  eapply Forall2_sym in H2.
  eapply Forall2_impl; [eapply Forall2_and|]; [exact H1|exact H2|].
  cbn; intros ? ? [? ?]. eapply H; assumption.
Qed.

#[global]
Instance cmp_global_instance_equiv Σ cmp_universe (hE : RelationClasses.Equivalence (cmp_universe Conv)) gr napp
  : RelationClasses.Equivalence (cmp_global_instance Σ cmp_universe Conv gr napp).
Proof.
  split.
  - intro. apply cmp_global_instance_refl; typeclasses eauto.
  - intros x y xy. eapply cmp_global_instance_sym; auto; typeclasses eauto.
  - intros x y z xy yz. eapply cmp_global_instance_trans; eauto; typeclasses eauto.
Qed.

Lemma cmp_universe_variance_antisym cmp_universe pb (hRe : RelationClasses.Equivalence (cmp_universe Conv)) v u u' :
  RelationClasses.Antisymmetric _ (cmp_universe Conv) (cmp_universe pb) ->
  cmp_universe_variance cmp_universe pb v u u' ->
  cmp_universe_variance cmp_universe pb v u' u ->
  cmp_universe_variance cmp_universe Conv v u u'.
Proof.
  intro hAntisym.
  destruct v => //=.
  apply hAntisym.
Qed.

Lemma cmp_universe_instance_variance_antisym cmp_universe pb (hRe : RelationClasses.Equivalence (cmp_universe Conv)) l u v :
  RelationClasses.Antisymmetric _ (cmp_universe Conv) (cmp_universe pb) ->
  cmp_universe_instance_variance cmp_universe pb l u v ->
  cmp_universe_instance_variance cmp_universe pb l v u ->
  cmp_universe_instance_variance cmp_universe Conv l u v.
Proof.
  intro hAntisym.
  apply Forall3_antisymP. intros ???.
  now eapply cmp_universe_variance_antisym.
Qed.

#[global]
Instance cmp_global_instance_antisym Σ cmp_universe pb (hRe : RelationClasses.Equivalence (cmp_universe Conv)) gr napp :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Antisymmetric _ (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Antisymmetric _ (cmp_global_instance Σ cmp_universe Conv gr napp) (cmp_global_instance Σ cmp_universe pb gr napp).
Proof.
  intros hsub hR u v.
  unfold cmp_global_instance_gen, cmp_opt_variance.
  destruct global_variance_gen; auto.
  apply cmp_opt_variance_or_impl; auto.
  eapply cmp_universe_instance_variance_antisym; tea.
Qed.

Lemma eq_term_upto_univ_antisym Σ cmp_universe cmp_sort pb
  (univ_equi : RelationClasses.Equivalence (cmp_universe Conv))
  (sort_equi : RelationClasses.Equivalence (cmp_sort Conv)) :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Antisymmetric _ (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Antisymmetric _ (cmp_sort Conv) (cmp_sort pb) ->
  Antisymmetric (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) (eq_term_upto_univ Σ cmp_universe cmp_sort pb).
Proof.
  intros univ_sub univ_anisym sort_antisym u v. generalize 0; intros n h h'.
  induction u in v, n, h, h' |- * using term_forall_list_ind.
  all: simpl ; inversion h ; subst; inversion h' ;
       subst ; try constructor ; auto.
  all: try eapply RelationClasses.antisymmetry; eauto.
Qed.

#[global]
Instance leq_term_antisym {cf:checker_flags} Σ φ
  : Antisymmetric (eq_term Σ φ) (leq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_antisym; exact _.
Qed.

Lemma global_variance_napp_mon Σ gr {napp napp'} :
  napp <= napp' ->
  match global_variance Σ gr napp with
  | Variance v => global_variance Σ gr napp' = Variance v
  | AllEqual => True
  | AllIrrelevant => global_variance Σ gr napp' = AllIrrelevant
  end.
Proof.
  intros hnapp.
  rewrite /global_variance_gen.
  destruct gr => //=.
  - destruct lookup_inductive_gen as [[mdecl idec]|] => //=.
    destruct destArity as [[ctx s]|] => //=.
    elim: Nat.leb_spec => // cass.
    destruct ind_variance => //=.
    elim: Nat.leb_spec => //. lia.
  - destruct lookup_constructor_gen as [[[mdecl idecl] cdecl]|] => //=.
    elim: Nat.leb_spec => // cass.
    elim: Nat.leb_spec => //. lia.
Qed.

#[global]
Instance cmp_global_instance_impl_same_napp Σ cmp_universe cmp_universe' pb pb' gr napp :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  subrelation (cmp_global_instance Σ cmp_universe pb gr napp) (cmp_global_instance Σ cmp_universe' pb' gr napp).
Proof.
  intros sub_conv sub_pb u u'.
  unfold cmp_global_instance_gen, cmp_opt_variance.
  destruct global_variance_gen as [| |v] => //.
  1: now apply cmp_universe_instance_impl.

  intros [H | H]; [left | right].
  1: eapply cmp_universe_instance_impl; tea.
  eapply cmp_universe_instance_variance_impl; eassumption.
Qed.

#[global]
Instance cmp_global_instance_impl Σ cmp_universe cmp_universe' pb pb' gr napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  napp <= napp' ->
  subrelation (cmp_global_instance Σ cmp_universe pb gr napp) (cmp_global_instance Σ cmp_universe' pb' gr napp').
Proof.
  intros sub_conv sub_pb lenapp u u'.
  unfold cmp_global_instance_gen.
  move: (global_variance_napp_mon Σ gr lenapp).
  destruct global_variance_gen as [| |v] => //.
  all: [> intros _ | intros ->; cbn ..]; auto.
  1: intro H; apply: cmp_instance_opt_variance; move: H => /=.
  - now apply cmp_universe_instance_impl.
  - intros [H | H]; [left | right].
    1: eapply cmp_universe_instance_impl; tea.
    eapply cmp_universe_instance_variance_impl; eassumption.
Qed.

Lemma global_variance_empty gr napp env : env.(declarations) = [] -> global_variance env gr napp = AllEqual.
Proof.
  destruct env; cbn => ->. destruct gr; auto.
Qed.

(** Pure syntactic equality, without cumulative inductive types subtyping *)

#[global]
Instance cmp_global_instance_empty_impl Σ cmp_universe cmp_universe' pb pb' gr napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  subrelation (cmp_global_instance empty_global_env cmp_universe pb gr napp) (cmp_global_instance Σ cmp_universe' pb' gr napp').
Proof.
  intros he t t'.
  unfold cmp_global_instance_gen.
  rewrite global_variance_empty //.
  intro H; apply: cmp_instance_opt_variance; move: H => /=.
  now apply cmp_universe_instance_impl.
Qed.

Lemma onctx_eq_ctx_impl P ctx ctx' cmp_term cmp_term' pb pb' :
  onctx P ctx ->
  (forall x, P x -> forall y, cmp_term Conv x y -> cmp_term' Conv x y) ->
  (forall x, P x -> forall y, cmp_term pb x y -> cmp_term' pb' x y) ->
  eq_context_gen cmp_term pb ctx ctx' ->
  eq_context_gen cmp_term' pb' ctx ctx'.
Proof.
  intros onc HP HP' H1.
  induction H1; depelim onc; constructor; eauto; intuition auto; simpl in *.
  destruct o; depelim p; constructor; auto.
Qed.

#[global]
Instance eq_term_upto_univ_impl Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
  RelationClasses.subrelation (cmp_sort pb) (cmp_sort' pb') ->
  napp <= napp' ->
  subrelation (eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp) (eq_term_upto_univ_napp Σ cmp_universe' cmp_sort' pb' napp').
Proof.
  intros univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb hnapp t t'.
  induction t in napp, napp', hnapp, pb, pb', univ_sub_pb, sort_sub_pb, t' |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using cmp_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply IHt1. 4:eauto. all:auto with arith. eauto.
  - inversion 1; subst; constructor.
    eapply cmp_global_instance_impl. 4:eauto. all:auto.
  - inversion 1; subst; constructor.
    eapply cmp_global_instance_impl. 4:eauto. all:eauto.
  - inversion 1; subst; constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
    * eapply cmp_universe_instance_impl'; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
  - intros h; depelim h. depelim o; constructor; cbn in X; constructor; intuition eauto.
    solve_all.
Qed.

#[global]
Instance eq_term_upto_univ_empty_impl Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
  RelationClasses.subrelation (cmp_sort pb) (cmp_sort' pb') ->
  subrelation (eq_term_upto_univ_napp empty_global_env cmp_universe cmp_sort pb napp) (eq_term_upto_univ_napp Σ cmp_universe' cmp_sort' pb' napp').
Proof.
  intros univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb t t'.
  induction t in napp, napp', pb, pb', univ_sub_pb, sort_sub_pb, t' |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
        eauto using cmp_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply cmp_global_instance_empty_impl. 2:eauto. all:auto.
  - inversion 1; subst; constructor.
    eapply cmp_global_instance_empty_impl. 2:eauto. all:eauto.
  - inversion 1; subst; constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
    * eapply cmp_universe_instance_impl'; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
  - inversion 1; subst; constructor. depelim X1; cbn in X; constructor; intuition eauto.
    solve_all.
Qed.

#[global]
Instance eq_term_upto_univ_leq Σ cmp_universe cmp_sort pb napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  napp <= napp' ->
  subrelation (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv napp) (eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp').
Proof.
  intros H. eapply eq_term_upto_univ_impl; exact _.
Qed.

#[global]
Instance eq_term_leq_term {cf:checker_flags} Σ φ
  : subrelation (eq_term Σ φ) (leq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_leq; auto; exact _.
Qed.

#[global]
Instance leq_term_partial_order {cf:checker_flags} Σ φ
  : PartialOrder (eq_term Σ φ) (leq_term Σ φ).
Proof.
  split. intros eqxy; split; now eapply eq_term_leq_term.
  intros [xy yx].
  now eapply leq_term_antisym.
Qed.

#[global]
Hint Constructors PCUICConversion.All_decls_alpha_pb : pcuic.

Local Ltac lih :=
  lazymatch goal with
  | ih : forall Rle v n k, eq_term_upto_univ_napp _ _ _ _ ?u _ -> _
    |- eq_term_upto_univ _ _ _ (lift _ _ ?u) _ =>
    eapply ih
  end.

Lemma eq_term_upto_univ_lift Σ cmp_universe cmp_sort pb n n' k :
  Proper (eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb n' ==> eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb n') (lift n k).
Proof.
  intros u v e.
  induction u in n', v, n, k, e, pb |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try solve [cbn ; constructor ; try lih ; try assumption; solve_all].
  - cbn. destruct e as (? & ? & e & ?).
    constructor; unfold eq_predicate, eq_branches, eq_branch in *; simpl; !!solve_all.
    * rewrite -?(All2_length e).
      eapply hh; eauto.
    * rewrite (All2_length hh3). now eapply hh2.
  - cbn. constructor.
    pose proof (All2_length e). unfold eq_mfixpoint in *.
    solve_all. rewrite H. eauto.
  - cbn. constructor.
    pose proof (All2_length e). unfold eq_mfixpoint in *.
    solve_all. rewrite H. eauto.
  - cbn. constructor. depelim o; cbn in X; try constructor; cbn; intuition eauto.
    solve_all.
Qed.

Lemma compare_decls_lift_decl Σ cmp_universe cmp_sort pb n k :
  Proper (compare_decls (fun pb => eq_term_upto_univ Σ cmp_universe cmp_sort pb) pb ==> compare_decls (fun pb => eq_term_upto_univ Σ cmp_universe cmp_sort pb) pb) (lift_decl n k).
Proof.
  intros d d' []; constructor; cbn; auto.
  all: now eapply eq_term_upto_univ_lift.
Qed.

Lemma eq_context_upto_lift_context Σ cmp_universe cmp_sort pb n k :
  Proper (eq_context_upto Σ cmp_universe cmp_sort pb ==> eq_context_upto Σ cmp_universe cmp_sort pb) (lift_context n k).
Proof.
  intros Γ Δ.
  induction 1; rewrite -> ?lift_context_snoc0. constructor.
  constructor; auto.
  rewrite -(All2_fold_length X).
  now eapply compare_decls_lift_decl.
Qed.

Lemma lift_compare_term `{checker_flags} Σ ϕ pb n k t t' :
  compare_term Σ ϕ pb t t' -> compare_term Σ ϕ pb (lift n k t) (lift n k t').
Proof.
  now apply eq_term_upto_univ_lift.
Qed.

Lemma lift_compare_decls `{checker_flags} pb Σ ϕ n k d d' :
  compare_decl pb Σ ϕ d d' -> compare_decl pb Σ ϕ (lift_decl n k d) (lift_decl n k d').
Proof.
  now apply compare_decls_lift_decl.
Qed.

Lemma lift_compare_context `{checker_flags} pb Σ φ l l' n k :
  compare_context pb Σ φ l l' ->
  compare_context pb Σ φ (lift_context n k l) (lift_context n k l').
Proof.
  now apply eq_context_upto_lift_context.
Qed.

Lemma lift_eq_term {cf:checker_flags} Σ φ n k T U :
  eq_term Σ φ T U -> eq_term Σ φ (lift n k T) (lift n k U).
Proof.
  apply eq_term_upto_univ_lift.
Qed.

Lemma lift_leq_term {cf:checker_flags} Σ φ n k T U :
  leq_term Σ φ T U -> leq_term Σ φ (lift n k T) (lift n k U).
Proof.
  apply eq_term_upto_univ_lift.
Qed.

Local Ltac sih :=
  lazymatch goal with
  | ih : forall Rle v n x y, _ -> eq_term_upto_univ _ _ _ ?u _ -> _ -> _
    |- eq_term_upto_univ _ _ _ (subst _ _ ?u) _ => eapply ih
  end.

Lemma eq_term_upto_univ_substs Σ cmp_universe cmp_sort pb napp :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  forall u v n l l',
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp u v ->
    All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) l l' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (subst l n u) (subst l' n v).
Proof.
  unfold RelationClasses.subrelation; intros hsub hsub' u v n l l' hu hl.
  induction u in napp, v, n, l, l', hu, hl, pb, hsub, hsub' |- * using term_forall_list_ind.
  all: dependent destruction hu.
  all: try solve [ cbn ; constructor ; try sih ; eauto ].
  - cbn. destruct (Nat.leb_spec0 n n0).
    + case_eq (nth_error l (n0 - n)).
      * intros t e. eapply All2_nth_error_Some in e as h ; eauto.
        destruct h as [t' [e' h]].
        rewrite e'.
        eapply eq_term_upto_univ_lift.
        eapply eq_term_upto_univ_leq. 4:eauto. all:auto with arith.
      * intros h. eapply All2_nth_error_None in h as hh ; eauto.
        rewrite hh.
        apply All2_length in hl as e. rewrite <- e.
        constructor.
    + constructor.
  - cbn. constructor. solve_all.
  - cbn.
    destruct e as (? & ? & e & ?).
    constructor ; unfold eq_predicate, eq_branches, eq_branch in *; simpl; try sih ; solve_all.
    * rewrite -(All2_length e). eapply e2; eauto.
    * rewrite (All2_length a0). now eapply b0.
  - cbn. constructor ; try sih ; eauto.
    pose proof (All2_length e). unfold eq_mfixpoint in *.
    solve_all. now rewrite H.
  - cbn. constructor ; try sih ; eauto.
    pose proof (All2_length e). unfold eq_mfixpoint in *.
    solve_all. now rewrite H.
  - cbn; constructor. depelim o; cbn in X |- *; constructor; cbn; intuition eauto.
    solve_all.
Qed.

Lemma eq_term_upto_univ_subst Σ cmp_universe cmp_sort pb :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  forall u v n x y,
    eq_term_upto_univ Σ cmp_universe cmp_sort pb u v ->
    eq_term_upto_univ Σ cmp_universe cmp_sort Conv x y ->
    eq_term_upto_univ Σ cmp_universe cmp_sort pb (u{n := x}) (v{n := y}).
Proof.
  intros hsub hsub' u v n x y e1 e2.
  eapply eq_term_upto_univ_substs; eauto.
Qed.

Lemma subst_eq_term {cf:checker_flags} Σ φ l k T U :
  eq_term Σ φ T U ->
  eq_term Σ φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply eq_term_upto_univ_substs; try easy.
Qed.

Lemma subst_leq_term {cf:checker_flags} Σ φ l k T U :
  leq_term Σ φ T U ->
  leq_term Σ φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply eq_term_upto_univ_substs; try easy.
  - intro; apply eq_leq_universe.
  - intro; apply eq_leq_sort.
Qed.

(** ** Behavior on mkApps and it_mkLambda_or_LetIn **  *)

Lemma eq_term_eq_term_napp Σ cmp_universe cmp_sort pb napp t t' :
  eq_term_upto_univ Σ cmp_universe cmp_sort pb t t' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t t'.
Proof.
  intros. eapply eq_term_upto_univ_impl. 6:eauto.
  5:auto with arith. all:typeclasses eauto.
Qed.

Lemma leq_term_leq_term_napp Σ cmp_universe cmp_sort pb napp t t' :
  eq_term_upto_univ Σ cmp_universe cmp_sort pb t t' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t t'.
Proof.
  intros. eapply eq_term_upto_univ_impl. 6:eauto.
  5:auto with arith. all:try typeclasses eauto.
Qed.

Lemma eq_term_upto_univ_napp_mkApps Σ cmp_universe cmp_sort pb u1 l1 u2 l2 napp :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb (#|l1| + napp) u1 u2 ->
    All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) l1 l2 ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros hu hl. induction l1 in napp, u1, u2, l2, hu, hl |- *.
  - inversion hl. subst. assumption.
  - inversion hl. subst. simpl.
    eapply IHl1.
    + constructor. all: assumption.
    + assumption.
Qed.

Lemma eq_term_upto_univ_napp_mkApps_l_inv Σ cmp_universe cmp_sort pb napp u l t :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (mkApps u l) t ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb (#|l| + napp) u u' *
      All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) l l' *
      (t = mkApps u' l').
Proof.
  intros h. induction l in napp, u, t, h, pb |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h. apply IHl in h as [u' [l' [[h1 h2] h3]]].
    dependent destruction h1. subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma eq_term_upto_univ_napp_mkApps_r_inv Σ cmp_universe cmp_sort pb napp u l t :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t (mkApps u l) ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb (#|l| + napp) u' u *
      All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) l' l *
      (t = mkApps u' l').
Proof.
  intros h. induction l in napp, u, t, h, pb |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h. apply IHl in h as [u' [l' [[h1 h2] h3]]].
    dependent destruction h1. subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma eq_term_upto_univ_mkApps Σ cmp_universe cmp_sort pb u1 l1 u2 l2 :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb #|l1| u1 u2 ->
    All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) l1 l2 ->
    eq_term_upto_univ Σ cmp_universe cmp_sort pb (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros; apply eq_term_upto_univ_napp_mkApps; rewrite ?Nat.add_0_r; auto.
Qed.

Lemma eq_term_upto_univ_mkApps_l_inv Σ cmp_universe cmp_sort pb u l t :
    eq_term_upto_univ Σ cmp_universe cmp_sort pb (mkApps u l) t ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb #|l| u u' *
      All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) l l' *
      (t = mkApps u' l').
Proof.
  intros H; apply eq_term_upto_univ_napp_mkApps_l_inv in H; rewrite ?Nat.add_0_r in H; auto.
Qed.

Lemma eq_term_upto_univ_mkApps_r_inv Σ cmp_universe cmp_sort pb u l t :
    eq_term_upto_univ Σ cmp_universe cmp_sort pb t (mkApps u l) ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb #|l| u' u *
      All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) l' l *
      (t = mkApps u' l').
Proof.
  intros H; apply eq_term_upto_univ_napp_mkApps_r_inv in H;
    rewrite Nat.add_0_r in H; auto.
Qed.

Lemma cmp_universe_instance_eq {u u'} : cmp_universe_instance eq u u' -> u = u'.
Proof.
  intros H.
  unfold cmp_universe_instance, on_rel in H.
  apply Forall2_map in H.
  apply Forall2_eq in H. apply map_inj in H ; revgoals.
  { intros ?? e. now inv e. }
  subst. constructor ; auto.
Qed.

Lemma valid_constraints_empty {cf} i :
  valid_constraints (empty_ext empty_global_env) (subst_instance_cstrs i (empty_ext empty_global_env)).
Proof.
  red. destruct check_univs => //.
Qed.

Lemma upto_eq_impl Σ cmp_universe cmp_sort pb0 pb :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  subrelation (eq_term_upto_univ Σ (fun _ => eq) (fun _ => eq) pb0) (eq_term_upto_univ Σ cmp_universe cmp_sort pb).
Proof.
  intros univ_refl univ_refl' sort_refl sort_refl'. eapply eq_term_upto_univ_impl. 5:auto.
  all: intros ? ? []; eauto.
Qed.

(** ** Syntactic ws_cumul_pb up to printing anotations ** *)

Definition upto_names := eq_term_upto_univ empty_global_env (fun _ => eq) (fun _ => eq) Conv.

Infix "≡" := upto_names (at level 70).

Infix "≡'" := (eq_term_upto_univ empty_global_env (fun _ => eq) (fun _ => eq) Conv) (at level 70).
Notation upto_names' := (eq_term_upto_univ empty_global_env (fun _ => eq) (fun _ => eq) Conv).

#[global]
Instance upto_names_ref : Reflexive upto_names.
Proof.
  eapply eq_term_upto_univ_refl; exact _.
Qed.

#[global]
Instance upto_names_sym : Symmetric upto_names.
Proof.
  eapply eq_term_upto_univ_sym; exact _.
Qed.

#[global]
Instance upto_names_trans : Transitive upto_names.
Proof.
  eapply eq_term_upto_univ_trans; exact _.
Qed.

(* TODO: rename *)
(* Definition nleq_term t t' := *)
(*   eqb_term_upto_univ eqb eqb t t'. *)

(* Corollary reflect_upto_names : *)
(*   forall t t', reflectT (upto_names t t') (nleq_term t t'). *)
(* Proof. *)
(*   intros t t'. eapply reflect_eq_term_upto_univ. *)
(*   all: intros u u'; eapply reflect_reflectT, eqb_spec. *)
(* Qed. *)

Lemma upto_names_impl Σ cmp_universe cmp_sort pb napp :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  subrelation upto_names (eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp).
Proof.
  intros univ_refl univ_refl' sort_refl sort_refl'.
  eapply eq_term_upto_univ_empty_impl; auto.
  all: intros ? ? []; eauto.
Qed.

Lemma upto_names_impl_eq_term {cf:checker_flags} Σ φ u v :
    u ≡ v -> eq_term Σ φ u v.
Proof.
  eapply upto_names_impl ; exact _.
Qed.

Lemma upto_names_impl_leq_term {cf:checker_flags} Σ φ u v :
    u ≡ v -> leq_term Σ φ u v.
Proof.
  eapply upto_names_impl ; exact _.
Qed.

Lemma eq_term_upto_univ_isApp Σ cmp_universe cmp_sort pb napp u v :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp u v ->
  isApp u = isApp v.
Proof.
  induction 1.
  all: reflexivity.
Qed.

(** ** ws_cumul_pb on contexts ** *)

Inductive rel_option {A B} (R : A -> B -> Type) : option A -> option B -> Type :=
| rel_some : forall a b, R a b -> rel_option R (Some a) (Some b)
| rel_none : rel_option R None None.

Derive Signature NoConfusion for rel_option.

Definition eq_decl_upto_gen Σ cmp_universe cmp_sort pb d d' : Type :=
  eq_binder_annot d.(decl_name) d'.(decl_name) *
  rel_option (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) d.(decl_body) d'.(decl_body) *
  eq_term_upto_univ Σ cmp_universe cmp_sort pb d.(decl_type) d'.(decl_type).

(* TODO perhaps should be def *)
Lemma All2_eq_context_upto Σ cmp_universe cmp_sort pb :
  subrelation (All2 (eq_decl_upto_gen Σ cmp_universe cmp_sort pb)) (eq_context_upto Σ cmp_universe cmp_sort pb).
Proof.
  intros Γ Δ h.
  induction h.
  - constructor.
  - destruct r as [[h1 h2] h3].
    destruct x as [na bo ty], y as [na' bo' ty'].
    simpl in h1, h2.
    destruct h2.
    + constructor ; eauto. constructor; auto.
    + constructor ; eauto. constructor; auto.
Qed.


Lemma eq_context_upto_impl Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
  RelationClasses.subrelation (cmp_sort pb) (cmp_sort' pb') ->
  subrelation (eq_context_upto Σ cmp_universe cmp_sort pb) (eq_context_upto Σ cmp_universe' cmp_sort' pb').
Proof.
  intros.
  apply eq_context_gen_impl.
  all: apply eq_term_upto_univ_impl; tc.
  all: auto.
Qed.

Lemma eq_context_upto_refl Σ cmp_universe cmp_sort pb :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  Reflexive (eq_context_upto Σ cmp_universe cmp_sort pb).
Proof. exact _. Qed.

Lemma eq_context_upto_sym Σ cmp_universe cmp_sort pb :
  RelationClasses.Symmetric (cmp_universe Conv) ->
  RelationClasses.Symmetric (cmp_universe pb) ->
  RelationClasses.Symmetric (cmp_sort Conv) ->
  RelationClasses.Symmetric (cmp_sort pb) ->
  Symmetric (eq_context_upto Σ cmp_universe cmp_sort pb).
Proof. exact _. Qed.

Lemma eq_context_upto_cat Σ cmp_universe cmp_sort pb Γ Δ Γ' Δ' :
  eq_context_upto Σ cmp_universe cmp_sort pb Γ Γ' ->
  eq_context_upto Σ cmp_universe cmp_sort pb Δ Δ' ->
  eq_context_upto Σ cmp_universe cmp_sort pb (Γ ,,, Δ) (Γ' ,,, Δ').
Proof. intros. eapply All2_fold_app; eauto. Qed.

Lemma eq_context_upto_rev Σ cmp_universe cmp_sort pb Γ Δ :
  eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ ->
  eq_context_upto Σ cmp_universe cmp_sort pb (rev Γ) (rev Δ).
Proof.
  induction 1.
  - constructor.
  - rewrite 2!rev_cons. eapply eq_context_upto_cat ; eauto.
    constructor ; eauto. constructor.
Qed.

Lemma eq_context_upto_rev' :
  forall Σ Γ Δ cmp_universe cmp_sort pb,
    eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ ->
    eq_context_upto Σ cmp_universe cmp_sort pb (List.rev Γ) (List.rev Δ).
Proof.
  intros Σ Γ Δ cmp_universe cmp_sort pb h.
  induction h.
  - constructor.
  - simpl. eapply eq_context_upto_cat.
    + repeat constructor; assumption.
    + assumption.
Qed.

Lemma eq_context_upto_length {Σ cmp_universe cmp_sort pb Γ Δ} :
    eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ ->
    #|Γ| = #|Δ|.
Proof.
  apply All2_fold_length.
Qed.

Lemma eq_context_upto_subst_context Σ cmp_universe cmp_sort pb :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  forall u v n l l',
    eq_context_upto Σ cmp_universe cmp_sort pb u v ->
    All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) l l' ->
    eq_context_upto Σ cmp_universe cmp_sort pb (subst_context l n u) (subst_context l' n v).
Proof.
  intros re u v n l l'.
  induction 1; intros Hl.
  - rewrite !subst_context_nil. constructor.
  - rewrite !subst_context_snoc; constructor; eauto.
    depelim p; constructor; simpl; intuition auto;
    rewrite -(length_of X);
    apply eq_term_upto_univ_substs; auto. all: reflexivity.
Qed.

#[global]
Hint Resolve All2_fold_nil : pcuic.

Lemma eq_context_upto_smash_context Σ ctx ctx' x y pb :
  eq_context_upto Σ (fun _ => eq) (fun _ => eq) pb ctx ctx' -> eq_context_upto Σ (fun _ => eq) (fun _ => eq) pb x y ->
  eq_context_upto Σ (fun _ => eq) (fun _ => eq) pb (smash_context ctx x) (smash_context ctx' y).
Proof.
  induction x in ctx, ctx', y |- *; intros eqctx eqt; inv eqt; simpl;
    try split; auto; try constructor; auto. depelim X0 => /=.
  - apply IHx; auto. apply eq_context_upto_cat; auto.
    constructor; pcuic.
  - apply IHx; auto. eapply eq_context_upto_subst_context; eauto.
    all: reflexivity.
Qed.

Lemma eq_context_upto_nth_error Σ cmp_universe cmp_sort pb ctx ctx' n :
  eq_context_upto Σ cmp_universe cmp_sort pb ctx ctx' ->
  rel_option (eq_decl_upto_gen Σ cmp_universe cmp_sort pb) (nth_error ctx n) (nth_error ctx' n).
Proof.
  induction 1 in n |- *.
  - rewrite nth_error_nil. constructor.
  - destruct n; simpl; auto.
    constructor. depelim p; constructor; intuition auto;
    now constructor.
Qed.

Lemma eq_context_impl :
  forall Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb',
    RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
    RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
    RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
    RelationClasses.subrelation (cmp_sort pb) (cmp_sort' pb') ->
    subrelation (eq_context_upto Σ cmp_universe cmp_sort pb) (eq_context_upto Σ cmp_universe' cmp_sort' pb').
Proof.
  intros Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb Γ Δ h.
  induction h.
  - constructor.
  - constructor; auto.
    depelim p; constructor; auto.
    all:eapply eq_term_upto_univ_impl; [ .. | eassumption]; eauto.
Qed.

Lemma eq_term_upto_univ_it_mkLambda_or_LetIn Σ cmp_universe cmp_sort pb :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  Proper (eq_context_upto Σ cmp_universe cmp_sort Conv ==> eq_term_upto_univ Σ cmp_universe cmp_sort Conv ==> eq_term_upto_univ Σ cmp_universe cmp_sort pb) it_mkLambda_or_LetIn.
Proof.
  intros ?? Γ Δ eq u v h.
  induction eq in u, v, h |- *.
  - cbn.
    eapply eq_term_upto_univ_leq; trea.
  - simpl. cbn. apply IHeq => //.
    destruct p; cbn; constructor ; tas; try reflexivity.
Qed.

Lemma eq_term_upto_univ_it_mkLambda_or_LetIn_r Σ cmp_universe cmp_sort Γ :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  respectful (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) (eq_term_upto_univ Σ cmp_universe cmp_sort Conv)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Proof.
  intros univ_refl sort_refl u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
Qed.

Lemma eq_term_it_mkLambda_or_LetIn {cf:checker_flags} Σ φ Γ :
  respectful (eq_term Σ φ) (eq_term Σ φ)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Proof.
  apply eq_term_upto_univ_it_mkLambda_or_LetIn_r; exact _.
Qed.

Lemma eq_term_upto_univ_it_mkProd_or_LetIn Σ cmp_universe cmp_sort Γ :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  respectful (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) (eq_term_upto_univ Σ cmp_universe cmp_sort Conv)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Proof.
  intros univ_refl sort_refl u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
Qed.

Lemma eq_term_it_mkProd_or_LetIn {cf:checker_flags} Σ φ Γ:
  respectful (eq_term Σ φ) (eq_term Σ φ)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Proof.
  eapply eq_term_upto_univ_it_mkProd_or_LetIn ; exact _.
Qed.

Lemma eq_term_it_mkLambda_or_LetIn_inv {cf:checker_flags} Σ φ Γ u v :
    eq_term Σ φ (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v) ->
    eq_term Σ  φ u v.
Proof.
  revert u v. induction Γ as [| [na [b|] A] Γ ih ] ; intros u v h.
  - assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
Qed.

Lemma eq_term_upto_univ_mkApps_inv Σ cmp_universe cmp_sort pb u l u' l' :
  isApp u = false ->
  isApp u' = false ->
  eq_term_upto_univ Σ cmp_universe cmp_sort pb (mkApps u l) (mkApps u' l') ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb #|l| u u' * All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) l l'.
Proof.
  intros hu hu' h.
  apply eq_term_upto_univ_mkApps_l_inv in h as hh.
  destruct hh as [v [args [[h1 h2] h3]]].
  apply eq_term_upto_univ_isApp in h1 as hh1. rewrite hu in hh1.
  apply mkApps_notApp_inj in h3 ; auto.
  destruct h3 as [? ?]. subst. split ; auto.
Qed.

Lemma isLambda_eq_term_l Σ cmp_universe cmp_sort pb u v :
    isLambda u ->
    eq_term_upto_univ Σ cmp_universe cmp_sort pb u v ->
    isLambda v.
Proof.
  intros h e.
  destruct u; try discriminate.
  depelim e. auto.
Qed.

Lemma isLambda_eq_term_r Σ cmp_universe cmp_sort pb u v :
    isLambda v ->
    eq_term_upto_univ Σ cmp_universe cmp_sort pb u v ->
    isLambda u.
Proof.
  intros h e.
  destruct v ; try discriminate.
  depelim e. auto.
Qed.

Lemma isConstruct_app_eq_term_l Σ cmp_universe cmp_sort pb u v :
    isConstruct_app u ->
    eq_term_upto_univ Σ cmp_universe cmp_sort pb u v ->
    isConstruct_app v.
Proof.
  intros h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e1 in h. cbn in h.
  rewrite e2. cbn.
  destruct t1 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply eq_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - reflexivity.
  - eapply decompose_app_notApp. eassumption.
Qed.

Lemma isConstruct_app_eq_term_r :
  forall Σ cmp_universe cmp_sort pb u v,
    isConstruct_app v ->
    eq_term_upto_univ Σ cmp_universe cmp_sort pb u v ->
    isConstruct_app u.
Proof.
  intros Σ cmp_universe cmp_sort pb u v h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e2 in h. cbn in h.
  rewrite e1. cbn.
  destruct t2 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply eq_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - eapply decompose_app_notApp. eassumption.
  - reflexivity.
Qed.

Lemma cmp_universe_variance_flip cmp_universe cmp_universe' pb pb' v u u' :
  RelationClasses.subrelation (cmp_universe Conv) (flip (cmp_universe' Conv)) ->
  RelationClasses.subrelation (cmp_universe pb) (flip (cmp_universe' pb')) ->
  cmp_universe_variance cmp_universe pb v u u' ->
  cmp_universe_variance cmp_universe' pb' v u' u.
Proof.
  intros conv_sym pb_sym.
  destruct v => //=.
  all: unfold on_rel, flip in *; now auto.
Qed.

Lemma cmp_universe_instance_variance_flip cmp_universe cmp_universe' pb pb' v u u' :
  RelationClasses.subrelation (cmp_universe Conv) (flip (cmp_universe' Conv)) ->
  RelationClasses.subrelation (cmp_universe pb) (flip (cmp_universe' pb')) ->
  cmp_universe_instance_variance cmp_universe pb v u u' ->
  cmp_universe_instance_variance cmp_universe' pb' v u' u.
Proof.
  intros conv_sym pb_sym H.
  induction H; constructor; eauto.
  now eapply cmp_universe_variance_flip.
Qed.


Lemma cmp_universe_instance_flip eq_universe eq_universe' u u' :
  RelationClasses.subrelation eq_universe (flip eq_universe') ->
  cmp_universe_instance eq_universe u u' ->
  cmp_universe_instance eq_universe' u' u.
Proof.
  intros Hsub H.
  apply Forall2_sym, Forall2_impl with (1 := H).
  intros ??. apply Hsub.
Qed.

Lemma cmp_global_instance_flip Σ cmp_universe cmp_universe' pb pb' gr napp u u':
  RelationClasses.subrelation (cmp_universe Conv) (flip (cmp_universe' Conv)) ->
  RelationClasses.subrelation (cmp_universe pb) (flip (cmp_universe' pb')) ->
  cmp_global_instance Σ cmp_universe pb gr napp u u' ->
  cmp_global_instance Σ cmp_universe' pb' gr napp u' u.
Proof.
  intros conv_sym pb_sym.
  unfold cmp_global_instance_gen, cmp_opt_variance.
  destruct global_variance_gen as [| |v] => //.
  2: intros [H|H]; [left|right]; move:H.
  1,2: apply cmp_universe_instance_flip; tas; reflexivity.
  now apply cmp_universe_instance_variance_flip.
Qed.

Lemma eq_term_upto_univ_napp_flip Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' napp u v :
  RelationClasses.subrelation (cmp_universe Conv) (flip (cmp_universe' Conv)) ->
  RelationClasses.subrelation (cmp_universe pb) (flip (cmp_universe' pb')) ->
  RelationClasses.subrelation (cmp_sort Conv) (flip (cmp_sort' Conv)) ->
  RelationClasses.subrelation (cmp_sort pb) (flip (cmp_sort' pb')) ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe' cmp_sort' pb' napp v u.
Proof.
  intros univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb.
  induction u in napp, pb, pb', univ_sub_pb, sort_sub_pb, v |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using cmp_universe_instance_flip; try (symmetry; assumption); fail).
  - inversion 1; subst; constructor.
    eapply All2_sym, All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor. now eapply sort_sub_pb.
  - inversion 1; subst; constructor.
    eapply cmp_global_instance_flip. 3:eauto. all:auto.
  - inversion 1; subst; constructor.
    eapply cmp_global_instance_flip. 3:eauto. all:eauto.
  - inversion 1; subst; constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto.
    solve_all.
    * apply All2_sym; solve_all.
    * eapply cmp_universe_instance_flip; eauto.
    * symmetry. solve_all.
    * apply All2_sym. solve_all. symmetry. solve_all.
  - inversion 1; subst; constructor.
    eapply All2_sym, All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto. now symmetry.
  - inversion 1; subst; constructor.
    eapply All2_sym, All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto. now symmetry.
  - inversion 1; subst; constructor. depelim X1; tas; try now constructor.
    destruct X as (hty & hdef & harr).
    constructor; eauto.
    1: now eapply univ_sub_conv.
    apply All2_sym; solve_all.
Qed.

Lemma eq_context_upto_flip Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' Γ Δ :
  RelationClasses.subrelation (cmp_universe Conv) (flip (cmp_universe' Conv)) ->
  RelationClasses.subrelation (cmp_universe pb) (flip (cmp_universe' pb')) ->
  RelationClasses.subrelation (cmp_sort Conv) (flip (cmp_sort' Conv)) ->
  RelationClasses.subrelation (cmp_sort pb) (flip (cmp_sort' pb')) ->
  eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ ->
  eq_context_upto Σ cmp_universe' cmp_sort' pb' Δ Γ.
Proof.
  intros univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb H.
  eapply All2_fold_flip, All2_fold_impl with (1 := H). clear H.
  intros _ _ d d' H.
  destruct H; constructor.
  all: try solve [ eapply eq_term_upto_univ_napp_flip; [ .. | eassumption]; assumption ].
  all: now symmetry.
Qed.

(** ws_cumul_pb of binder annotations *)
Notation eq_annots Γ Δ :=
  (Forall2 (fun na decl => eq_binder_annot na (decl_name decl)) Γ Δ).

Lemma eq_context_upto_names_binder_annot Γ Δ :
  eq_context_upto_names Γ Δ -> eq_annots (forget_types Γ) Δ.
Proof.
  induction 1; constructor; auto.
  destruct r; auto.
Qed.

Lemma eq_annots_fold (Γ : list aname) (f : nat -> term -> term) (Δ : context) :
  eq_annots Γ (fold_context_k f Δ) <-> eq_annots Γ Δ.
Proof.
  induction Δ in Γ |- *.
  - cbn; auto. reflexivity.
  - rewrite fold_context_k_snoc0 /=.
    destruct Γ; split; intros H; depelim H; constructor; auto;
    now apply IHΔ.
Qed.

Lemma eq_annots_subst_context (Γ : list aname) s k (Δ : context) :
  eq_annots Γ (subst_context s k Δ) <-> eq_annots Γ Δ.
Proof.
  apply eq_annots_fold.
Qed.

Lemma eq_annots_lift_context (Γ : list aname) n k (Δ : context) :
  eq_annots Γ (lift_context n k Δ) <-> eq_annots Γ Δ.
Proof.
  apply eq_annots_fold.
Qed.

#[global]
Instance Forall2_ext {A B} :
  Proper (pointwise_relation A (pointwise_relation B iff) ==> eq ==> eq ==> iff) (@Forall2 A B).
Proof.
  intros f g Hfg ?? -> ?? ->.
  split; intro; eapply Forall2_impl; tea; apply Hfg.
Qed.

Lemma eq_annots_subst_instance_ctx (Γ : list aname) u (Δ : context) :
  eq_annots Γ Δ@[u] <-> eq_annots Γ Δ.
Proof.
  etransitivity. eapply Forall2_map_right.
  eapply Forall2_ext; auto.
  intros x y; reflexivity.
Qed.

Lemma eq_annots_inst_case_context (Γ : list aname) pars puinst (ctx : context) :
  eq_annots Γ ctx <->
  eq_annots Γ (PCUICCases.inst_case_context pars puinst ctx).
Proof.
  etransitivity. symmetry; eapply (eq_annots_subst_instance_ctx _ puinst).
  etransitivity.
  symmetry; eapply (eq_annots_subst_context _ (List.rev pars) 0).
  reflexivity.
Qed.

Lemma eq_context_gen_map2_set_binder_name cmp_term cmp_term' pb pb' pctx pctx' Γ Δ :
  eq_context_gen cmp_term pb pctx pctx' ->
  eq_context_gen cmp_term' pb' Γ Δ ->
  eq_context_gen cmp_term' pb'
    (map2 set_binder_name (forget_types pctx) Γ)
    (map2 set_binder_name (forget_types pctx') Δ).
Proof using Type.
  intros eqp.
  induction 1 in pctx, pctx', eqp |- *.
  - destruct eqp; cbn; constructor.
  - destruct eqp; simpl; constructor; auto.
    destruct c, p; constructor; auto.
Qed.

Lemma eq_context_upto_names_map2_set_binder_name cmp_term pb pctx pctx' Γ Δ :
  eq_context_upto_names pctx pctx' ->
  eq_context_gen cmp_term pb Γ Δ ->
  eq_context_gen cmp_term pb
    (map2 set_binder_name (forget_types pctx) Γ)
    (map2 set_binder_name (forget_types pctx') Δ).
Proof using Type.
  intro eqctx.
  eapply eq_context_gen_map2_set_binder_name with (pb := Conv).
  now apply eq_context_upto_names_gen.
Qed.

Lemma eq_context_upto_names_map2_set_binder_name_eq nas Γ Δ :
  eq_context_upto_names Γ Δ ->
  map2 PCUICEnvironment.set_binder_name nas Γ =
  map2 PCUICEnvironment.set_binder_name nas Δ.
Proof.
  induction 1 in nas |- *; cbn; auto.
  destruct nas; cbn; auto.
  f_equal. destruct r; subst; unfold set_binder_name; f_equal.
  apply IHX.
Qed.

Lemma trans_eq_context_upto_names trans Γ Δ :
  eq_context_upto_names Γ Δ ->
  eq_context_upto_names (map (map_decl trans) Γ) (map (map_decl trans) Δ).
Proof.
  intro.
  eapply All2_map. solve_all.
  destruct X; cbn; subst; constructor; auto.
Qed.

Lemma eq_context_upto_names_fold (f : nat -> term -> term) Γ Δ :
  eq_context_upto_names Γ Δ ->
  eq_context_upto_names (fold_context_k f Γ) (fold_context_k f Δ).
Proof.
  induction 1.
  - cbn; auto.
  - rewrite !fold_context_k_snoc0 /=.
    constructor; auto.
    rewrite -(All2_length X).
    destruct r; now constructor.
Qed.

Lemma eq_context_upto_names_smash_context {Γ Δ} :
  eq_context_upto_names Γ Δ ->
  eq_context_upto_names (smash_context [] Γ) (smash_context [] Δ).
Proof.
  assert (eq_context_upto_names [] []) as X by constructor. move: X.
  set (Γ0 := []) at 1 3. set (Δ0 := []). clearbody Γ0 Δ0. intro X.
  induction 1 in Γ0, Δ0, X |- *; cbn; try constructor; tas.
  destruct r; cbn; apply IHX0.
  - apply All2_app; tas. repeat constructor. assumption.
  - now apply eq_context_upto_names_fold.
Qed.
