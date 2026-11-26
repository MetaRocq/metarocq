(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst.
From MetaRocq.Erasure Require Import EAst EAstUtils EGlobalEnv EInduction.

From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

(** * First-order values of erased programs

  First-order values are trees of constructors. Two representations are
  used along the erasure pipeline:
  - [firstorder_evalue]: constructors applied to their parameters and
    arguments, before parameters are stripped and constructors are turned
    into blocks;
  - [firstorder_evalue_block]: constructor blocks, without parameters. *)

Inductive firstorder_evalue Σ : EAst.term -> Prop :=
  | is_fo i n args npars nargs :
  EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (npars, nargs) ->
  Forall (firstorder_evalue Σ) (skipn npars args) ->
  #|args| = npars + nargs ->
  firstorder_evalue Σ (EAst.mkApps (EAst.tConstruct i n []) args).

Lemma list_size_skipn {A} (l : list A) size n :
  list_size size (skipn n l) <= list_size size l.
Proof.
  induction n in l |- *.
  - rewrite skipn_0 //.
  - destruct l. rewrite skipn_nil. now cbn.
    rewrite skipn_S. cbn. specialize (IHn l); lia.
Qed.

Section elim.
  Context (Σ : global_context).
  Context (P : EAst.term -> Prop).
  Context (ih : (forall i n args npars nargs,
    EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (npars, nargs) ->
    Forall (firstorder_evalue Σ) (skipn npars args) ->
    Forall P (skipn npars args) ->
    #|args| = npars + nargs ->
    P (EAst.mkApps (EAst.tConstruct i n []) args))).

  Equations? firstorder_evalue_elim (t : EAst.term)
    (fo : firstorder_evalue Σ t) : P t by wf t (MR lt EInduction.size) :=
  { | _, is_fo i n args npars nargs hl hf hargs => _ }.
  Proof.
    eapply ih; tea.
    eapply In_Forall. intros x hin.
    eapply (proj1 (Forall_forall _ _)) in hf; tea.
    apply firstorder_evalue_elim => //. red.
    rewrite EInduction.size_mkApps.
    eapply (In_size id EInduction.size) in hin.
    unfold id in *.
    pose proof (list_size_skipn args EInduction.size npars).
    change (fun x => EInduction.size x) with EInduction.size in hin.
    clear -hin H.
    eapply Nat.lt_le_trans; tea. cbn. lia.
  Qed.
End elim.

Derive Signature for firstorder_evalue.

Inductive firstorder_evalue_block Σ : EAst.term -> Prop :=
  | is_fo_block i n args :
    EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (0, #|args|) ->
    Forall (firstorder_evalue_block Σ) args ->
    firstorder_evalue_block Σ (EAst.tConstruct i n args).

Lemma firstorder_evalue_block_elim Σ {P : EAst.term -> Prop} :
  (forall i n args,
    EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (0, #|args|) ->
    Forall (firstorder_evalue_block Σ) args ->
    Forall P args ->
    P (EAst.tConstruct i n args)) ->
  forall t, firstorder_evalue_block Σ t -> P t.
Proof.
  intros Hf.
  fix aux 2.
  intros t fo; destruct fo.
  eapply Hf => //. clear H. rename H0 into H.
  move: args H.
  fix aux' 2.
  intros args []; constructor.
  now apply aux. now apply aux'.
Qed.

(** ** Environment extension *)

Lemma firstorder_evalue_extends Σ Σ' t :
  extends Σ Σ' ->
  firstorder_evalue Σ t ->
  firstorder_evalue Σ' t.
Proof.
  intros ext; move: t.
  apply: firstorder_evalue_elim => i n args npars nargs hl hf hargs ih.
  econstructor; tea.
  red in ext.
  move: hl; rewrite /lookup_constructor_pars_args /lookup_constructor
    /lookup_inductive /lookup_minductive.
  move: (ext (inductive_mind i)).
  now case: lookup_env => // a; move/(_ _ eq_refl) ->.
Qed.

Lemma firstorder_evalue_block_extends Σ Σ' t :
  extends Σ Σ' ->
  firstorder_evalue_block Σ t ->
  firstorder_evalue_block Σ' t.
Proof.
  intros ext; move: t.
  apply: firstorder_evalue_block_elim => i n args hl hf ih.
  constructor; tea.
  red in ext.
  move: hl; rewrite /lookup_constructor_pars_args /lookup_constructor
    /lookup_inductive /lookup_minductive.
  move: (ext (inductive_mind i)).
  now case: lookup_env => // a; move/(_ _ eq_refl) ->.
Qed.

(** ** Values of inductive types

  Values built only from constructors of inductive (not coinductive) types,
  in the constructors-as-blocks representation. *)

Section FirstorderInd.
  Context (Σ : global_declarations).

  Unset Elimination Schemes.
  Inductive firstorder_ind_value : term -> Type :=
  | firstorder_ind_value_block ind c args :
    EGlobalEnv.is_coind Σ (inductive_mind ind) = false ->
    All firstorder_ind_value args ->
    firstorder_ind_value (tConstruct ind c args).
  Set Elimination Schemes.

  Lemma firstorder_ind_value_rect (P : term -> Type) :
    (forall ind c args,
      EGlobalEnv.is_coind Σ (inductive_mind ind) = false ->
      All firstorder_ind_value args -> All P args ->
      P (tConstruct ind c args)) ->
    forall v, firstorder_ind_value v -> P v.
  Proof using Type.
    intros H. fix aux 2. intros v [ind c args hco hargs]. apply H => //.
    clear -aux hargs. induction hargs; constructor; auto.
  Qed.
End FirstorderInd.

(** The predicate only depends on which inductive types are coinductive. *)
Lemma firstorder_ind_value_is_coind Σ Σ' v :
  (forall kn, EGlobalEnv.is_coind Σ' kn = EGlobalEnv.is_coind Σ kn) ->
  ∥ firstorder_ind_value Σ v ∥ -> ∥ firstorder_ind_value Σ' v ∥.
Proof.
  intros hco [h]. sq. revert v h.
  apply: firstorder_ind_value_rect.
  intros ind c args hc hargs IH. constructor => //. now rewrite hco.
Qed.
