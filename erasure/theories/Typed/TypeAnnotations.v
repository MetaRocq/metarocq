From MetaRocq.Erasure.Typed Require Import Annotations.
From MetaRocq.Erasure.Typed Require Import Utils.
From MetaRocq.Erasure.Typed Require Import Erasure.
From MetaRocq.Erasure.Typed Require Import ExAst.
From MetaRocq.Erasure.Typed Require Import Extraction.
From MetaRocq.Erasure.Typed Require Import Optimize.
From MetaRocq.Erasure.Typed Require Import Transform.
From MetaRocq.Utils Require Import ResultMonad.
Local Set Warnings "-warn-library-file-stdlib-vector".
From Stdlib Require Import VectorDef.
From Equations Require Import Equations.
From MetaRocq.Erasure Require Import Extract.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils.
From MetaRocq.PCUIC Require Import PCUICInversion.
From MetaRocq.PCUIC Require Import PCUICLiftSubst.
From MetaRocq.PCUIC Require Import PCUICTyping.
From MetaRocq.PCUIC Require Import PCUICValidity.
From MetaRocq.PCUIC Require Import PCUICSafeLemmata.
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl.
From MetaRocq.SafeChecker Require Import PCUICSafeRetyping.
From MetaRocq.SafeChecker Require Import PCUICWfEnv.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Kernames.

Import VectorNotations.

Open Scope list.
Set Equations Transparent.

Section fix_env.
Opaque flag_of_type erase_type.

Context (Σ : global_env_ext).
Context (wfextΣ : ∥wf_ext Σ∥).
Lemma wfΣ : ∥wf Σ∥.
Proof. now sq. Qed.

Import config.

Implicit Types (cf : checker_flags).
Existing Instance extraction_checker_flags.
Existing Instance PCUICSN.extraction_normalizing.

Existing Instance fake_guard_impl_instance.

Program Definition flag_of_type_impl := @flag_of_type canonical_abstract_env_impl (ltac:(now unshelve econstructor;eauto))
  PCUICSN.extraction_normalizing _.
Next Obligation. apply fake_normalization; eauto. Qed.

Definition length_app_transparent {A} (l1 l2 : list A) :
  #|l1| + #|l2| = #|l1 ++ l2|.
induction l1.
- reflexivity.
- cbn. now rewrite IHl1.
Defined.

Definition mapi_length_transparent {A B} {f : nat -> A -> B} (l : list A) : forall n, #|mapi_rec f l n| = #|l|.
induction l;intros.
- reflexivity.
- cbn. now rewrite IHl.
Defined.

Definition Sn_plus_one_transparent {n} : S n = n + 1.
now induction n. Defined.

(* NOTE: borrowed from metarocq's MRList. There it's defined for some other [rev] *)
Definition length_rev_transparent {A} (l : list A) :
  #|List.rev l| = #|l|.
induction l.
  - reflexivity.
  - cbn. rewrite <- length_app_transparent.
    cbn. rewrite IHl. symmetry. apply Sn_plus_one_transparent.
Defined.

Definition rev_mapi_length_app {A B} {f : nat -> A -> B} (l1 : list A) (l2 : list B) :
  #|List.rev l1| + #|l2| = #|List.rev (mapi f l1) ++ l2|.
transitivity (#|List.rev (mapi f l1)| + #|l2|).
repeat rewrite length_rev_transparent.
unfold mapi. rewrite mapi_length_transparent;reflexivity.
apply length_app_transparent.
Defined.

Section annotate.
  Context {A : Type}.
  Context (annotate_types :
             forall Γ (erΓ : Vector.t tRel_kind #|Γ|) t (Ht : welltyped Σ Γ t) et (er : erases Σ Γ t et), annots A et).

  Equations? (noeqns) annotate_branches
           Γ
           (erΓ : Vector.t tRel_kind #|Γ|)
           (brs : list (branch term))
           (ebrs : list (list name × E.term))
           (pr : predicate term)
           (wf : Forall2 (fun '(mk_branch Γ0 t) '(_, et) =>
                            let Γ0 := inst_case_context (pparams pr) (puinst pr) Γ0 in
                            welltyped Σ (Γ,,,Γ0) t /\ erases Σ (Γ,,,Γ0) t et) brs ebrs)
    : bigprod (annots A ∘ snd) ebrs by struct ebrs :=
    annotate_branches Γ _ _ [] _ _ := tt;
    annotate_branches Γ erΓ ((mk_branch Γ0 t) :: brs) ((_, et) :: ebrs) _ wf :=
      let Γ0 := inst_case_context (pparams pr) (puinst pr) Γ0 in
      let erΓ1 := Vector.append (Vector.const RelOther #|Γ0|) erΓ in
      (annotate_types (Γ,,,Γ0) (Vector.cast erΓ1 (length_app_transparent _ _)) t _ et _, annotate_branches Γ _ brs ebrs pr _);
    annotate_branches _ _ _ _ _ _ := !.
  Proof. all: try now depelim wf. Defined.


  (** Determines whether a type var should be created on the base of [last_var_level].
      Returns the corresponding entry of [tRel_kind] and the next type var level. *)
  Definition type_flag_to_tRel_kind {Γ T}
             (tf : type_flag Σ Γ T)
             (last_var_level : option nat) : tRel_kind * option nat :=
    match tf with
    | {| is_logical := false; conv_ar := inl _ |} =>
        (* non-logical arity becomes a type var *)
        match last_var_level with
        | Some last_vl =>
            let next_vl := 1 + last_vl in
            (RelTypeVar next_vl, Some next_vl)
        | None => (RelTypeVar 0, Some 0)
        end
    | _ => (RelOther, last_var_level)
    end.

  (** Traverse the erased context to get the last type variable level (the last one was
      added on top of the context, so it's the first hit.) *)
  Equations get_last_type_var {n} (vs : Vector.t Erasure.tRel_kind n) : option nat :=
    get_last_type_var []%vector := None;
    get_last_type_var (RelTypeVar i :: _)%vector := Some i;
    get_last_type_var (_ :: vs0)%vector := get_last_type_var vs0.

  Equations? (noeqns) context_to_erased
           (Γ0 : context)
           (var_level : option nat)
           (mfix : list (def term))
           (wt : Forall (fun d => ∥ isType Σ Γ0 (dtype d) ∥) mfix) : Vector.t tRel_kind #|mfix| :=
    context_to_erased _ _ [] _ := []%vector;
    context_to_erased Γ0 vl (d :: Γ1) _ :=
      let '(i, next_vl) :=
        type_flag_to_tRel_kind
         (flag_of_type_impl Σ _ Γ0 (dtype d) _) vl in
      (i :: context_to_erased Γ0 next_vl Γ1 _)%vector.
  Proof. all: inversion wt;subst;eauto. Qed.

  Equations? (noeqns) annotate_defs
           Γ
           (erΓ : Vector.t tRel_kind #|Γ|)
           (defs : list (def term))
           (edefs : list (E.def E.term))
           (wf : Forall2 (fun d ed => welltyped Σ Γ (dbody d) /\ erases Σ Γ (dbody d) (E.dbody ed))
                         defs edefs)
    : bigprod (annots A ∘ E.dbody) edefs by struct edefs :=
    annotate_defs Γ _ _ [] _ := tt;
    annotate_defs Γ _ (d :: defs) (ed :: edefs) wf :=
      (annotate_types Γ erΓ (dbody d) _ (E.dbody ed) _, annotate_defs Γ erΓ defs edefs _);
    annotate_defs _ _ _ _ _ := !.
  Proof.
    all: now depelim wf.
  Qed.
End annotate.

Fixpoint vec_repeat {A} (a : A) (n : nat) : Vector.t A n :=
  match n with
  | 0 => []%vector
  | S n => (a :: vec_repeat a n)%vector
  end.

Existing Instance PCUICSN.extraction_normalizing.

#[program] Definition type_of_impl :=
  @type_of _ PCUICSN.extraction_normalizing canonical_abstract_env_impl (ltac:(now unshelve econstructor;eauto))
    _.
Next Obligation.
  apply fake_normalization; eauto.
Qed.

#[program] Definition erase_type_aux_impl :=
  @erase_type_aux canonical_abstract_env_impl (ltac:(now unshelve econstructor;eauto)) PCUICSN.extraction_normalizing _.
Next Obligation.
  apply fake_normalization; eauto.
Qed.

Program Definition erase_type_of Γ erΓ t (wt : welltyped Σ Γ t) : box_type :=
  let ty := type_of_impl Γ _ t _ in
  let flag := flag_of_type_impl Σ _ Γ ty _ in
  if conv_ar flag then
    TBox
  else
    let next_type_var :=
      match get_last_type_var erΓ with
      | Some tv => 1 + tv
      | None => 0
      end in
    (erase_type_aux_impl Σ _ Γ erΓ ty _ (Some next_type_var)).2.
Next Obligation.
  destruct wt. sq;eapply typing_wf_local; eauto.
Qed.
Next Obligation.
  destruct wt. sq.
  assert (wf Σ).
  { now apply wf_ext_wf. }
  apply BDFromPCUIC.typing_infering in X as [?[??]].
  econstructor;eauto.
Qed.
Next Obligation.
  assert (∥ wf Σ ∥).
  {sq. now apply wf_ext_wf. }
  destruct wt.
  unfold type_of_impl,type_of.
  unfold PCUICSafeRetyping.principal_type_type.
  remember (infer _ _ _ _ _ _) as infT.
  destruct infer as [T tyT]. rewrite HeqinfT. clear HeqinfT. cbn.
  specialize (tyT Σ eq_refl).
  sq. eapply BDToPCUIC.infering_typing in tyT;eauto.
  eapply validity; eauto.
  eapply typing_wf_local; eauto.
Qed.
Next Obligation.
  assert (∥ wf Σ ∥).
  { destruct wfextΣ. sq; now apply wf_ext_wf. }
  destruct wt.
  unfold type_of_impl,type_of.
  unfold PCUICSafeRetyping.principal_type_type.
  destruct infer as [T tyT];cbn in *.
  specialize (tyT Σ eq_refl).
  sq. eapply BDToPCUIC.infering_typing in tyT;eauto.
  eapply validity; eauto.
  eapply typing_wf_local; eauto.
Qed.

Lemma Forall_mapi :
  forall {A B : Type} {n} (P : B -> Prop) (f : nat -> A -> B)
    (l : list A),
  Forall ( fun x => forall i : nat, P (f i x)) l ->
  Forall P (mapi_rec f l n).
Proof.
  intros A B n P f l H.
  generalize dependent n.
  induction l; intros n.
  - constructor.
  - cbn. inversion H;subst. constructor;auto.
Qed.

Equations? (noeqns) annotate_types
         (Γ : context)
         (erΓ : Vector.t tRel_kind #|Γ|)
         (t : term) (wt : welltyped Σ Γ t)
         (et : E.term)
         (er : erases Σ Γ t et) : annots box_type et by struct et :=
(* For some reason 'with' hangs forever so we need 'where' here *)
annotate_types Γ erΓ t wt et er := annot (erase_type_of Γ erΓ t wt) et t wt er
where annot
        (bt : box_type)
        (et : E.term)
        (t : term) (wt : welltyped Σ Γ t)
        (er : erases Σ Γ t et) : annots box_type et := {
annot bt E.tBox _ _ _ => bt;
annot bt (E.tRel _) _ _ er0 => bt;
annot bt (E.tVar _) _ _ er0 => bt;
annot bt (E.tEvar _ ets) _ wt0 er0 => !;
annot bt (E.tLambda na eB) (tLambda na' A B) wt0 er0 =>
  let last_vl := get_last_type_var erΓ in
  let (i, _) := type_flag_to_tRel_kind (flag_of_type_impl Σ eq_refl Γ A _) last_vl in
  let erΓ1 := (i :: erΓ)%vector in
  (bt, annotate_types (Γ,, vass na' A) erΓ1 B _ eB _);
annot bt (E.tLetIn na eb eb') (tLetIn na' b ty b') wt0 er0 =>
  let last_vl := get_last_type_var erΓ in
  let (i, _) := type_flag_to_tRel_kind (flag_of_type_impl Σ eq_refl Γ ty _) last_vl in
  let erΓ1 := (i :: erΓ)%vector in
  (bt, (annotate_types Γ erΓ b _ eb _, annotate_types (Γ,, vdef na' b ty) erΓ1 b' _ eb' _));
annot bt (E.tApp ehd earg) (tApp hd arg) wt0 er0 =>
  (bt, (annotate_types Γ erΓ hd _ ehd _, annotate_types Γ erΓ arg _ earg _));
annot bt (E.tConst _) _ wt0 er0 => bt;
annot bt (E.tConstruct _ _ _) _ wt0 er0 => bt; (* NOTE: we ignore the arguments if constructors-as-block is enabled *)
annot bt (E.tCase _ ediscr ebrs) (tCase _ pr discr brs) wt0 er0 =>
  (bt, (annotate_types Γ erΓ discr _ ediscr _, annotate_branches annotate_types Γ erΓ brs ebrs pr _));
annot bt (E.tProj _ et0) (tProj _ t0) wt0 er0 => (bt, annotate_types Γ erΓ t0 _ et0 _);
annot bt (E.tFix edefs _) (tFix defs _) wt0 er0 =>
  let last_vl := get_last_type_var erΓ in
  let erΓ1 := Vector.append (context_to_erased Γ last_vl (List.rev defs) _) erΓ in
  (bt, annotate_defs annotate_types (Γ,,, fix_context defs) (VectorEq.cast erΓ1 (rev_mapi_length_app _ _)) defs edefs _);
annot bt (E.tCoFix edefs _) (tCoFix defs _) wt0 er0 =>
  let last_vl := get_last_type_var erΓ in
  let erΓ1 := Vector.append (context_to_erased Γ last_vl (List.rev defs) _) erΓ in
  (bt, annotate_defs annotate_types (Γ,,, fix_context defs) (VectorEq.cast erΓ1 (rev_mapi_length_app _ _)) defs edefs _);
annot bt (E.tPrim _) _ _ _ => bt; (* TODO *)
annot bt _ _ wt0 er0 => !
}.
Proof.
  all: try solve [inversion er0; auto].
  all: try destruct wt0.
  all: try destruct wfextΣ as [[]].
  all: try subst erΓ1.
  - depelim er0.
    now apply inversion_Evar in X.
  - apply inversion_Lambda in X as (? & h1 & ? & ?); auto.
    now apply isTypeRel_isType in h1.
  - apply inversion_Lambda in X as (? & h1 & ? & ?); auto.
    apply isTypeRel_isType in h1.
    econstructor; eauto.
  - apply inversion_LetIn in X as (?&h1&?&?); auto.
    now apply lift_sorting_forget_body, isTypeRel_isType in h1.
  - apply inversion_LetIn in X as (?&?&?&?); auto.
    econstructor; eapply unlift_TermTyp; eauto.
  - apply inversion_LetIn in X as (?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_App in X as (?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_App in X as (?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_Case in X as (?&?&?&?&?&?); cbn in *;auto.
    inversion c.
    econstructor; eauto.
  - apply inversion_Case in X as (?&?&?&?&?&?); cbn in *;auto.
    destruct c as [??].
    depelim er0.
    clear -brs_ty X.
    eapply All2_Forall2.
    eapply All2i_All2_All2; tea. cbn.
    clear X brs_ty.
    intros n x1 y [bcontext bbody] [?[?[??]]].
    cbn in *. unfold pre_case_branch_context_gen,inst_case_branch_context in *;cbn in *.
    remember (case_branch_type _ _ _ _ _ _ _ _).1 as Γ0.
    intros [].
    destruct y as [bctx bbody'].
    split;[|now auto].
    eexists.
    pose proof (eqctx := PCUICCasesContexts.inst_case_branch_context_eq (p := pr) (br := {| bbody := bbody'; bcontext := bctx |}) a).
    cbn in eqctx. unfold case_branch_context, case_branch_context_gen in eqctx. cbn in eqctx.
    unfold case_branch_type in HeqΓ0. cbn in HeqΓ0.
    rewrite eqctx in HeqΓ0. unfold inst_case_branch_context in HeqΓ0. cbn in HeqΓ0. rewrite <-HeqΓ0. exact t.
  - apply inversion_Proj in X as (?&?&?&?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_Fix in X as (?&?&?&?&?&?&?); auto.
    apply rev_Forall.
    apply All_Forall.
    eapply All_impl. apply a.
    intros d X. cbn in *. apply isTypeRel_isType in X. now constructor.
  - apply inversion_Fix in t0 as (?&?&?&?&?&?&?); auto.
    depelim er0.
    clear -a0 X.
    eapply All2_All_mix_left in X; eauto.
    clear -X.
    revert X.
    unfold on_def_body.
    generalize (Γ,,, fix_context defs).
    clear Γ.
    intros Γ a.
    induction a; [now constructor|].
    constructor; [|now eauto].
    destruct r as [?[??]].
    apply unlift_TermTyp in l0.
    split; [|now auto].
    econstructor; eauto.
  - apply inversion_CoFix in X as (?&?&?&?&?&?&?); auto.
    apply rev_Forall.
    apply All_Forall.
    eapply All_impl. apply a.
    intros d X. cbn in *. apply isTypeRel_isType in X. now constructor.
  - apply inversion_CoFix in t0 as (?&?&?&?&?&?&?); auto.
    depelim er0.
    clear -a0 X.
    eapply All2_All_mix_left in X; eauto.
    clear -X.
    revert X.
    unfold on_def_body.
    generalize (Γ,,, fix_context defs).
    clear Γ.
    intros Γ1 a.
    induction a; [now constructor|].
    constructor; [|now eauto].
    destruct r as (? & ? & ? & ?).
    apply unlift_TermTyp in l0.
    split; [|now auto].
    econstructor; eauto.
Qed.

#[program] Definition erase_constant_decl_impl X_type X :=
  @erase_constant_decl X_type X PCUICSN.extraction_normalizing _.
Next Obligation. apply Erasure.fake_normalization; eauto. Defined.

Definition annotate_types_erase_constant_decl X_type X cst wt eq :
  match erase_constant_decl_impl X_type X Σ eq cst wt with
  | inl cst => constant_body_annots box_type cst
  | _ => unit
  end.
Proof.
  unfold erase_constant_decl_impl,erase_constant_decl,erase_constant_decl_clause_1.
  destruct flag_of_type.
  cbn in *.
  destruct conv_ar.
  - destruct cst; cbn.
    destruct cst_body0; exact tt.
  - destruct cst; cbn.
    destruct cst_body0; [|exact tt].
    cbn.
    apply (annotate_types [] []%vector t); [|apply ErasureFunction.erases_erase].
    cbn in *.
    destruct wt. apply unlift_TermTyp in X0.
    econstructor; eauto.
    exact eq.
Defined.

(* Context (nin : forall Σ : global_env_ext, wf_ext Σ -> Σ ∼_ext X -> PCUICSN.NormalizationIn Σ). *)
Definition annotate_types_erase_global_decl X_type X eq kn decl wt :
  global_decl_annots box_type (@erase_global_decl X_type X Σ eq kn decl wt).
Proof.
  unfold erase_global_decl.
  destruct decl; [|exact tt].
  cbn.
  pose proof (annotate_types_erase_constant_decl X_type X c wt).
  unfold erase_constant_decl_impl in *. cbn in X0.
  specialize (X0 eq).
  cbn. destruct erase_constant_decl; [|exact tt].
  cbn. exact X0.
Defined.

End fix_env.

Definition annotate_types_erase_global_decls_deps_recursive X_type X Σ universes retros wfΣ include ignore_deps :
  env_annots box_type (@erase_global_decls_deps_recursive X_type X Σ universes retros wfΣ include ignore_deps).
Proof.
  revert include.
  induction Σ in X, X_type, wfΣ |- *; intros include; [exact tt|].
  cbn in *.
  destruct a.
  destruct KernameSet.mem.
  - cbn.
    match goal with
    | |- context[ @erase_global_decl ?X_type ?X ?a ?b ?c ?d ?e] =>
      unshelve epose proof (annotate_types_erase_global_decl a _ X_type X b c d e)
    end.
    { eapply abstract_eq_wf in wfΣ as [equiv [wf]].
      eapply (sq_wf_pop_decl _ _ _ _ (sq wf)); cbn; trea. }
    match goal with
    | |- context[erase_global_decls_deps_recursive _ _ _ ?prf ?incl _] =>
      specialize (IHΣ _ _ prf incl )
    end.
    exact (X0, IHΣ).
  - match goal with
    | |- context[erase_global_decls_deps_recursive _ _ _ ?prf ?incl _] =>
      specialize (IHΣ _ _ prf incl)
    end.
    exact IHΣ.
Defined.

Import EAst.
Definition annot_dearg_lambdas {A} mask {t} (ta : annots A t)
  : annots A (dearg_lambdas mask t).
Proof.
  revert t ta mask.
  fix f 1.
  intros [] ta mask; cbn in *; try exact ta.
  - destruct mask; [exact ta|].
    destruct b.
    + apply annot_subst1; [exact ta.1|].
      apply (f _ ta.2).
    + exact (ta.1, f _ ta.2 _).
  - exact (ta.1, (ta.2.1, f _ ta.2.2 _)).
Defined.

(** [dummy] is used to annotate boxes that a substituted for dead arguments *)
Definition annot_dearg_branch_aux {A} i (dummy : A) mask {t} (ta : annots A t)
  : annots A (dearg_branch_body_rec i mask t).2.
Proof.
  revert mask t ta i.
  fix f 1.
  intros [] t ta i; cbn in *; try exact ta.
  destruct b.
  - apply f.
    apply annot_subst1.
    exact dummy.
    exact ta.
  - exact (f _ _ ta _).
Defined.

Definition annot_dearg_branch {A} := @annot_dearg_branch_aux A 0.

Definition annot_dearg_single
           mask
           {hd}
           (hda : annots box_type hd)
           {args}
           (argsa : All (fun t => box_type * annots box_type t) args)
  : annots box_type (dearg_single mask hd args).
Proof.
  revert hd hda args argsa.
  induction mask; intros hd hda args argsa; cbn.
  - apply annot_mkApps; assumption.
  - destruct a.
    + (* arg is being removed but overall type does not change. *)
      destruct argsa.
      * (* there is no arg. Lambda has original type so body has type of codomain *)
        refine (annot hda, _).
        apply IHmask; [|exact All_nil].
        apply annot_lift.
        (* type of body is now the codomain *)
        exact (map_annot
                 (fun bt =>
                    match bt with
                    | TArr _ cod => cod
                    | _ => bt
                    end) hda).
      * (* arg was removed. We take the new type to be the old type of the application
         instead of the codomain as the old type of the application is more specialized. *)
        apply IHmask; [|exact argsa].
        exact (map_annot (fun _ => p.1) hda).
    + destruct argsa.
      * refine (annot hda, _).
        apply IHmask; [|exact All_nil].
        cbn.
        exact (match annot hda with
                | TArr dom cod => (cod, (annot_lift _ _ hda, dom))
                | t => (t, (annot_lift _ _ hda, t))
                end).
      * apply IHmask; [|exact argsa].
        exact (p.1, (hda, p.2)).
Defined.

Definition annot_dearg_case_branches
           {A}
           (dummy : A)
           mm i
           {brs} (brsa : bigprod (annots A ∘ snd) brs)
  : bigprod (annots A ∘ snd) (dearg_case_branches mm i brs).
Proof.
  destruct mm; [|exact brsa].
  cbn.
  apply bigprod_mapi_rec; [|exact brsa].
  intros.
  unfold dearg_case_branch.
  destruct (_ <=? _).
  * apply annot_dearg_branch.
    exact dummy.
    exact X.
  * exact X.
Defined.

Definition annot_dearg_aux
           im cm
           {args : list term}
           (argsa : All (fun t => box_type * annots box_type t) args)
           {t : term}
           (ta : annots box_type t) : annots box_type (dearg_aux im cm args t).
Proof.
  revert args argsa t ta.
  fix f 3.
  intros args argsa [] ta; cbn.
  - exact (annot_mkApps ta argsa).
  - exact (annot_mkApps ta argsa).
  - exact (annot_mkApps ta argsa).
  - apply annot_mkApps; [|exact argsa].
    cbn in *.
    refine (ta.1, bigprod_map _ ta.2).
    apply f.
    exact All_nil.
  - apply annot_mkApps; [|exact argsa].
    exact (ta.1, f _ All_nil _ ta.2).
  - apply annot_mkApps; [|exact argsa].
    exact (ta.1, (f _ All_nil _ ta.2.1, f _ All_nil _ ta.2.2)).
  - apply f; [|exact ta.2.1].
    apply All_cons; [|exact argsa].
    exact (ta.1, f _ All_nil _ ta.2.2).
  - exact (annot_dearg_single _ ta argsa).
  - exact (annot_dearg_single _ ta argsa).
  - destruct indn.
    refine (annot_mkApps _ argsa).
    cbn in *.
    refine (ta.1, _).
    refine (f _ All_nil _ ta.2.1, _).
    apply annot_dearg_case_branches.
    exact TBox. (* a dummy type for tBox that is substituted for dead arguments *)
    apply bigprod_map; [|exact ta.2.2].
    intros.
    exact (f _ All_nil _ X).
  - destruct p.
    refine (annot_mkApps _ argsa).
    refine (ta.1, _).
    exact (f _ All_nil _ ta.2).
  - refine (annot_mkApps _ argsa).
    refine (ta.1, _).
    fold (annots box_type).
    apply bigprod_map; [|exact ta.2].
    intros.
    exact (f _ All_nil _ X).
  - refine (annot_mkApps _ argsa).
    refine (ta.1, _).
    fold (annots box_type).
    apply bigprod_map; [|exact ta.2].
    intros.
    exact (f _ All_nil _ X).
  - refine (annot_mkApps _ argsa). cbn. cbn in ta. exact ta.
  - refine (annot_mkApps _ argsa). cbn. cbn in ta. exact ta.
  - refine (annot_mkApps _ argsa). cbn. cbn in ta. exact ta.
Defined.

Definition annot_dearg im cm {t : term} (ta : annots box_type t) : annots box_type (dearg im cm t) :=
  annot_dearg_aux im cm All_nil ta.

Definition annot_debox_type_decl Σ {decl} (a : global_decl_annots box_type decl)
  : global_decl_annots box_type (debox_type_decl Σ decl).
Proof.
  unfold debox_type_decl.
  destruct decl;[|exact a| (destruct o as [p|]; auto; destruct p;exact a)].
  cbn in *.
  (* we have removed type variables from inductives, so adjust type annotations similarly *)
  unfold constant_body_annots in *.
  cbn.
  destruct Ex.cst_body; [|exact tt].
  exact (map_annots (debox_box_type Σ) a).
Defined.

Definition annot_debox_env_types {Σ} (a : env_annots box_type Σ)
  : env_annots box_type (debox_env_types Σ).
Proof.
  unfold debox_env_types.
  apply bigprod_map; [|exact a].
  intros.
  apply annot_debox_type_decl.
  exact X.
Defined.

Definition annot_dearg_cst im cm kn {cst} (a : constant_body_annots box_type cst)
  : constant_body_annots box_type (dearg_cst im cm kn cst).
Proof.
  red in a |- *.
  unfold dearg_cst.
  cbn in *.
  destruct Annotations.Ex.cst_body; [|exact tt].
  cbn.
  apply annot_dearg.
  apply annot_dearg_lambdas.
  exact a.
Defined.

Definition annot_dearg_decl im cm kn {decl} (a : global_decl_annots box_type decl) :
  global_decl_annots box_type (dearg_decl im cm kn decl).
Proof.
  unfold dearg_decl.
  destruct decl; try exact a.
  cbn.
  apply annot_dearg_cst.
  exact a.
Defined.

Definition annot_dearg_env im cm {Σ} (a : env_annots box_type Σ)
  : env_annots box_type (dearg_env im cm Σ).
Proof.
  apply bigprod_map; [|exact a].
  intros ((? & ?) & ?) ?.
  cbn in *.
  apply annot_dearg_decl.
  exact X.
Defined.

Definition annot_dearg_transform
           (overridden_masks : kername -> option bitmask)
           (do_trim_const_masks : bool)
           (do_trim_ctor_masks : bool)
           (check_closed : bool)
           (check_expanded : bool)
           (check_valid_masks : bool) :
  annot_transform_type
    box_type
    (dearg_transform
       overridden_masks
       do_trim_const_masks do_trim_ctor_masks
       check_closed check_expanded check_valid_masks).
Proof.
  red.
  intros Σ a.
  red.
  unfold timed.
  destruct (_ && _); [exact tt|].
  destruct analyze_env.
  destruct (_ && _); [exact tt|].
  destruct (_ && _); [exact tt|].
  apply annot_debox_env_types.
  apply annot_dearg_env.
  exact a.
Defined.

Module AnnotOptimizePropDiscr.
  Import EOptimizePropDiscr OptimizePropDiscr.

  Definition annots_subst_tBox :
    forall (n : nat) (t0 : term),
      annots box_type t0 -> annots box_type (ECSubst.csubst tBox n t0).
  Proof.
    fix f 2.
    intros n t0.
    revert n.
    destruct t0;intros n0 bt;try exact bt.
    - cbn. destruct (n0 ?= n);exact (annot bt).
    - cbn. exact (bt.1, bigprod_map (f n0) bt.2).
    - cbn in *. exact (bt.1, f _ _ bt.2).
    - exact (bt.1, (f _ _ bt.2.1, f _ _ bt.2.2)).
    - exact (bt.1, (f _ _ bt.2.1, f _ _ bt.2.2)).
    - cbn in *.
      refine (bt.1, (f _ _ bt.2.1, _)).
      refine (bigprod_map _ bt.2.2).
      intros ? a'. apply (f _ _ a').
    - cbn in *. exact (bt.1, f _ _ bt.2).
    - refine (bt.1, bigprod_map _ bt.2).
      intros ? a'; exact (f _ _ a').
    - refine (bt.1, bigprod_map _ bt.2).
      intros ? a'; exact (f _ _ a').
  Defined.

  Definition annot_remove_match_on_box Σ {t} (a : annots box_type t) : annots box_type (remove_match_on_box Σ t).
  Proof.
    revert t a.
    fix f 1.
    intros [] a; cbn in *; try exact a.
    - exact (a.1, bigprod_map f a.2).
    - exact (a.1, f _ a.2).
    - exact (a.1, (f _ a.2.1, f _ a.2.2)).
    - exact (a.1, (f _ a.2.1, f _ a.2.2)).
    - assert (br_annots : bigprod (fun br => annots box_type br.2) (map (on_snd (remove_match_on_box Σ)) brs)).
      { refine (bigprod_map _ a.2.2).
        intros ? a'; apply (f _ a'). }
      unfold isprop_ind.
      destruct EEnvMap.GlobalContextMap.inductive_isprop_and_pars as [[]|]; cbn.
      destruct b;cbn.
      2-3: exact (a.1, (f _ a.2.1, br_annots)).
      destruct map as [|(?&?) []]; cbn in *.
      1,3: exact (a.1, (f _ a.2.1, br_annots)).
      (* Term changed from
         match e with
         | c a1 .. an => f
         end
         to a substitution of boxes into f
         (f[tBox/a1,..,tBox/an]) *)
      destruct br_annots as (fa&_).
      revert l t fa.
      clear.
      fix f 1.
      intros [] hd hda.
      + exact hda.
      + cbn.
        apply f.
        apply annots_subst_tBox.
        exact hda.
    - destruct EEnvMap.GlobalContextMap.inductive_isprop_and_pars as [[]|]; cbn.
      destruct b;cbn.
      2-3: exact (a.1, f _ a.2).
      exact a.1.
    - refine (a.1, bigprod_map _ a.2).
      intros ? a'; exact (f _ a').
    - refine (a.1, bigprod_map _ a.2).
      intros ? a'; exact (f _ a').
  Defined.

  Definition annot_remove_match_on_box_constant_body Σ {cst} (a : constant_body_annots box_type cst) :
    constant_body_annots box_type (remove_match_on_box_constant_body Σ cst).
  Proof.
    unfold constant_body_annots, remove_match_on_box_constant_body in *.
    cbn.
    destruct ExAst.cst_body; cbn; [|exact tt].
    apply annot_remove_match_on_box.
    exact a.
  Defined.

  Definition annot_remove_match_on_box_decl Σ {decl} (a : global_decl_annots box_type decl) :
    global_decl_annots box_type (remove_match_on_box_decl Σ decl).
  Proof.
    unfold global_decl_annots, remove_match_on_box_decl in *.
    destruct decl; [|exact tt|exact tt].
    apply annot_remove_match_on_box_constant_body.
    exact a.
  Defined.

  Definition annot_remove_match_on_box_env Σ fgΣ (a : env_annots box_type Σ) :
    env_annots box_type (remove_match_on_box_env Σ fgΣ).
  Proof.
    unfold env_annots, remove_match_on_box_env.
    apply bigprod_map.
    - intros.
      apply annot_remove_match_on_box_decl.
      exact X.
    - exact a.
  Defined.
End AnnotOptimizePropDiscr.

Definition annot_compose_transforms {Σ} (a : env_annots box_type Σ) transforms :
  All (annot_transform_type box_type) transforms ->
  match compose_transforms transforms Σ with
  | Ok Σ => env_annots box_type Σ
  | Err _ => unit
  end.
Proof.
  revert transforms Σ a.
  fix f 4.
  intros ? Σ a [].
  - exact a.
  - cbn.
    red in a0.
    specialize (a0 _ a).
    destruct x; [|exact tt].
    apply f; [exact a0|exact a1].
Defined.

Definition annot_extract_pcuic_env params Σ wfΣ include ignore :
  All (annot_transform_type box_type) (extract_transforms params) ->
  match extract_pcuic_env params Σ wfΣ include ignore with
  | Ok Σ => env_annots box_type Σ
  | _ => unit
  end.
Proof.
  intros all.
  unfold extract_pcuic_env.
  destruct optimize_prop_discr.
  + apply annot_compose_transforms; [|exact all].
    apply AnnotOptimizePropDiscr.annot_remove_match_on_box_env.
    apply annotate_types_erase_global_decls_deps_recursive.
  + apply annotate_types_erase_global_decls_deps_recursive.
Defined.

Definition annot_extract_template_env params Σ include ignore :
  All (annot_transform_type box_type) (extract_transforms (pcuic_args params)) ->
  match extract_template_env params Σ include ignore with
  | Ok Σ => env_annots box_type Σ
  | _ => unit
  end.
Proof.
  intros all.
  unfold extract_template_env,extract_template_env_general, check_wf_and_extract.
  cbn.
  destruct check_wf_env_func; [|exact tt]. cbn.
  apply annot_extract_pcuic_env.
  exact all.
Defined.

Definition annot_extract_template_env_within_coq Σ include ignore :
  match extract_template_env_within_coq Σ include ignore with
  | Ok Σ => env_annots box_type Σ
  | _ => unit
  end.
Proof.
  apply annot_extract_template_env.
  cbn.
  constructor; [|constructor].
  apply annot_dearg_transform.
Defined.

Definition annot_extract_template_env_within_coq_sig
           (Σ : Ast.Env.global_env)
           (include : KernameSet.t)
           (ignore : kername -> bool) : option (∑ Σ, env_annots box_type Σ).
Proof.
  pose proof (annot_extract_template_env_within_coq Σ include ignore).
  destruct extract_template_env_within_coq; [|exact None].
  exact (Some (t; X)).
Defined.
