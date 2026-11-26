(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Transform.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils.
From MetaRocq.PCUIC Require PCUICTyping PCUICFirstorder PCUICExpandLets
  PCUICExpandLetsCorrectness PCUICInductiveInversion PCUICValidity
  PCUICInversion PCUICSpine PCUICClassification PCUICWcbvEval.
From MetaRocq.Erasure Require EAst EAstUtils EGlobalEnv EWcbvEval
  EWellformed EWcbvEvalNamed EConstructorsAsBlocks ERemoveParams EFirstorder
  ECoInductiveToInductive EArities ErasureProperties Extract.
From MetaRocq.Erasure Require ErasureCorrectness.
From MetaRocq.Erasure Require Import EEnvMap.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure
  ErasureCorrectness.
From MetaRocq.ErasurePlugin.transforms Require Import GuardedToUnguardedFix
  RemoveParams ConstructorsAsBlocks.
Import MetaRocq.Common.Transform.Transform.

#[local] Existing Instance extraction_checker_flags.
#[local] Existing Instance PCUICSN.extraction_normalizing.

(** * Readback of first-order values to PCUIC

  The verified λ□ part of the pipeline ([verified_lambdabox_etransform])
  reads its first-order values back context-free, with [blocks_readback]. The
  part before it, erasure followed by the switch to unguarded fixpoints and
  the removal of constructor parameters, loses the parameters and the
  universe instances of constructors, so its readback is type-directed: it
  takes the PCUIC environment and the expected type of the value.

  The parameters and instance of a constructor are those of the expected
  type. The expected types of its arguments are computed from the type of
  the constructor, instantiated with these parameters and the arguments
  already read back, so nested values can have parameters too. The readback
  does not normalise types: it gives back exactly the values whose
  parameters are syntactically those of their expected types
  ([fo_value_at]). *)

(** Reduces the leading let-ins of [ty], at most [fuel] of them. *)
Fixpoint skip_lets (fuel : nat) (ty : term) : term :=
  match fuel, ty with
  | S fuel, tLetIn _ b _ B => skip_lets fuel (subst10 b B)
  | _, _ => ty
  end.

(** Instantiates the leading products of [ty] with [l]. *)
Fixpoint inst_spine (fuel : nat) (ty : term) (l : list term) : term :=
  match l with
  | [] => ty
  | a :: l =>
    match skip_lets fuel ty with
    | tProd _ _ B => inst_spine fuel (subst10 a B) l
    | ty' => ty'
    end
  end.

(** Enough fuel to go through the let-ins of a constructor type. *)
Definition cstr_fuel mdecl (cdecl : constructor_body) :=
  #|mdecl.(ind_params)| + #|cdecl.(cstr_args)|.

(** The type of the arguments of constructor [n] of [ind], at instance
    [u] and with parameters [pars]. *)
Definition cstr_args_type mdecl cdecl ind n u pars :=
  inst_spine (cstr_fuel mdecl cdecl)
    (PCUICTyping.type_of_constructor mdecl cdecl (ind, n) u) pars.

(** Readback of a first-order value in constructors-as-blocks form, at the
    expected type [T]. *)
Fixpoint readback_at (Σ : global_env) (T : term) (t : EAst.term)
  {struct t} : option term :=
  match t with
  | EAst.tConstruct ind n args =>
    match decompose_app T, lookup_constructor Σ ind n with
    | (tInd _ u, l), Some (mdecl, idecl, cdecl) =>
      let fuel := cstr_fuel mdecl cdecl in
      let pars := firstn mdecl.(ind_npars) l in
      let fix aux (ty : term) (l : list EAst.term) {struct l} :=
        match l with
        | [] => Some []
        | a :: l =>
          match skip_lets fuel ty with
          | tProd _ A B =>
            match readback_at Σ A a with
            | Some a' => option_map (cons a') (aux (subst10 a' B) l)
            | None => None
            end
          | _ => None
          end
        end in
      option_map (fun args' => mkApps (tConstruct ind n u) (pars ++ args'))
        (aux (cstr_args_type mdecl cdecl ind n u pars) args)
    | _, _ => None
    end
  | _ => None
  end.

(** The readback of the arguments of a constructor, as done by
    [readback_at]. *)
Fixpoint readback_args (Σ : global_env) (fuel : nat) (ty : term)
  (l : list EAst.term) : option (list term) :=
  match l with
  | [] => Some []
  | a :: l =>
    match skip_lets fuel ty with
    | tProd _ A B =>
      match readback_at Σ A a with
      | Some a' => option_map (cons a') (readback_args Σ fuel (subst10 a' B) l)
      | None => None
      end
    | _ => None
    end
  end.

Lemma readback_at_construct Σ T ind n args :
  readback_at Σ T (EAst.tConstruct ind n args) =
  match decompose_app T, lookup_constructor Σ ind n with
  | (tInd _ u, l), Some (mdecl, idecl, cdecl) =>
    let pars := firstn mdecl.(ind_npars) l in
    option_map (fun args' => mkApps (tConstruct ind n u) (pars ++ args'))
      (readback_args Σ (cstr_fuel mdecl cdecl)
        (cstr_args_type mdecl cdecl ind n u pars) args)
  | _, _ => None
  end.
Proof.
  cbn -[cstr_args_type]. destruct decompose_app as [[] ?] => //.
  destruct lookup_constructor as [[[mdecl idecl] cdecl]|] => //.
  f_equal. generalize (cstr_args_type mdecl cdecl ind n ui
    (firstn (ind_npars mdecl) l)).
  induction args => //= ty.
  destruct skip_lets => //. destruct readback_at => //.
  now rewrite IHargs.
Qed.

(** The readback of the erasure, unguarded fixpoints and parameter removal
    part of the pipeline, on its λ□ values (constructor applications without
    parameters) of expected type [T]. *)
Definition erase_readback (Σ : global_env) (T : term) (v : EAst.term) :
  option term :=
  readback_at Σ T (EConstructorsAsBlocks.compile_evalue_box v []).

(** The readback of the whole verified pipeline: the λ□ readback, then
    [erase_readback]. *)
Definition pipeline_readback econf (Σ : global_env) (T : term)
  (v : EAst.term) : option term :=
  match ETransform.readback (verified_lambdabox_etransform econf) v with
  | Some v' => erase_readback Σ T v'
  | None => None
  end.

(** [v] is a first-order value of expected type [T]: its parameters and
    instance are those of [T], and its arguments are first-order values of
    the expected types given by the type of its constructor. This is what
    the readback assumes about the parameters and universe instances erased
    by the pipeline. *)
Inductive fo_value_at (Σ : global_env) : term -> term -> Prop :=
| fo_value_at_C T ind' ind n u l args mdecl idecl cdecl :
  decompose_app T = (tInd ind' u, l) ->
  lookup_constructor Σ ind n = Some (mdecl, idecl, cdecl) ->
  mdecl.(ind_npars) <= #|l| ->
  fo_args_at Σ (cstr_fuel mdecl cdecl)
    (cstr_args_type mdecl cdecl ind n u (firstn mdecl.(ind_npars) l)) args ->
  fo_value_at Σ T
    (mkApps (tConstruct ind n u) (firstn mdecl.(ind_npars) l ++ args))
with fo_args_at (Σ : global_env) : nat -> term -> list term -> Prop :=
| fo_args_at_nil fuel ty : fo_args_at Σ fuel ty []
| fo_args_at_cons fuel ty na A B a args :
  skip_lets fuel ty = tProd na A B ->
  fo_value_at Σ A a ->
  fo_args_at Σ fuel (subst10 a B) args ->
  fo_args_at Σ fuel ty (a :: args).

Scheme fo_value_at_mut := Induction for fo_value_at Sort Prop
  with fo_args_at_mut := Induction for fo_args_at Sort Prop.

(** [readback_at] inverts the compilation of first-order values. *)
Lemma readback_at_compile (Σ : global_env) T v :
  fo_value_at Σ T v ->
  readback_at Σ T (compile_value_box Σ v []) = Some v.
Proof.
  move=> h.
  apply (fo_value_at_mut Σ
    (fun T v _ => readback_at Σ T (compile_value_box Σ v []) = Some v)
    (fun fuel ty args _ => readback_args Σ fuel ty
      (map (Basics.flip (compile_value_box Σ) []) args) = Some args)) => //.
  - intros T' ind' ind n u l args mdecl idecl cdecl hT hl hnp _ IH.
    have hnp' : pcuic_lookup_inductive_pars Σ ind = Some (ind_npars mdecl).
    { move: hl. rewrite /lookup_constructor /lookup_constructor_gen
        /lookup_inductive_gen /lookup_minductive_gen
        /pcuic_lookup_inductive_pars.
      destruct lookup_env as [[]|] => //.
      destruct nth_error => //. destruct nth_error => //.
      now intros [= -> _ _]. }
    rewrite (compile_value_box_mkApps hnp') app_nil_r map_app.
    have hlen : #|firstn (ind_npars mdecl) l| = ind_npars mdecl.
    { rewrite length_firstn. lia. }
    rewrite -{1}hlen
      -(length_map (Basics.flip (compile_value_box Σ) []) (firstn _ l))
      skipn_all_app.
    rewrite readback_at_construct hT hl. cbv zeta. now rewrite IH.
  - intros fuel ty na A B a args hs _ IHa _ IHargs.
    cbn. rewrite hs. rewrite /Basics.flip in IHa |- *.
    now rewrite IHa /= IHargs.
Qed.

(** * Values with arbitrary parameters

  The verified pipeline theorem ([verified_erasure_pipeline_theorem]) is
  stated for programs whose type is a first-order inductive
  ([PCUICFirstorder.firstorder_ind]): its parameters must have first-order
  types themselves and the arguments of its constructors parameterless
  first-order types. Types like [list nat] are excluded, as the argument of
  [cons] has the type of the parameter [A : Type].

  Erasure followed by the removal of constructor parameters forgets the
  parameters: from there on, the pipeline only deals with parameterless
  first-order values. The readback theorem is hence stated for values built
  from constructors of inductive types with arbitrary parameters
  ([fo_value_pars]), assumed of the value the program evaluates to. This
  includes the values of first-order inductive types
  ([fo_value_pars_firstorder_ind]). As the evaluation is assumed, the
  environment can contain axioms. *)

(** [v] is a tree of constructors of non-propositional, non-coinductive
    inductive types. The parameters of the constructors are arbitrary: only
    the arguments are required to be such trees. *)
Inductive fo_value_pars (Σ : global_env_ext) : term -> Prop :=
| fo_value_pars_C i n ui u args pandi mdecl idecl cdecl :
  declared_constructor Σ (i, n) mdecl idecl cdecl ->
  PCUICTyping.typing Σ [] (mkApps (tConstruct i n ui) args)
    (mkApps (tInd i u) pandi) ->
  ~~ PCUICFirstorder.isPropositional Σ i ->
  ind_finite mdecl <> CoFinite ->
  Forall (fo_value_pars Σ) (skipn (ind_npars mdecl) args) ->
  fo_value_pars Σ (mkApps (tConstruct i n ui) args).

Lemma fo_value_pars_ind' (Σ : global_env_ext) (P : term -> Prop) :
  (forall i n ui u args pandi mdecl idecl cdecl,
    declared_constructor Σ (i, n) mdecl idecl cdecl ->
    PCUICTyping.typing Σ [] (mkApps (tConstruct i n ui) args)
      (mkApps (tInd i u) pandi) ->
    ~~ PCUICFirstorder.isPropositional Σ i ->
    ind_finite mdecl <> CoFinite ->
    Forall (fun a => fo_value_pars Σ a /\ P a)
      (skipn (ind_npars mdecl) args) ->
    P (mkApps (tConstruct i n ui) args)) ->
  forall v, fo_value_pars Σ v -> P v.
Proof.
  intros H. fix IH 2.
  intros v [i n ui u args pandi mdecl idecl cdecl hd ht hp hf hargs].
  eapply H; tea. clear -IH hargs.
  revert hargs. generalize (skipn (ind_npars mdecl) args).
  fix aux 2. intros l [|x l' hx hl].
  - constructor.
  - constructor; [split; [exact hx|exact (IH _ hx)]|exact (aux _ hl)].
Qed.

(** ** First-order inductive types

  The values of first-order inductive types ([PCUICFirstorder]) satisfy
  [fo_value_pars]: the generalised theorem covers the original one. *)

Lemma firstorder_value_fo_value_pars (Σ : global_env_ext)
  {wfΣ : PCUICTyping.wf Σ} v :
  PCUICFirstorder.firstorder_value Σ [] v ->
  forall i u args,
  PCUICTyping.typing Σ [] v (mkApps (tInd i u) args) ->
  PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i ->
  fo_value_pars Σ v.
Proof.
  intros fo. move: v fo.
  apply: PCUICFirstorder.firstorder_value_inds.
  intros i n ui u args pandi hty hargs IH nprop i' u' args' Hty Hfo.
  apply PCUICValidity.inversion_mkApps in Hty as Hcon; auto.
  destruct Hcon as (?&typ_ctor& spine).
  apply PCUICInversion.inversion_Construct in typ_ctor
    as (?&?&?&?&?&?&?); auto.
  eapply @PCUICInductiveInversion.Construct_Ind_ind_eq
    with (mdecl := x0) in Hty as Hty'; eauto.
  destruct Hty' as (([[[]]] & ?)  & ? & ? & ? & ? & _). subst.
  eapply PCUICSpine.typing_spine_strengthen in spine. 3: eauto.
  2: eapply PCUICInductiveInversion.declared_constructor_valid_ty; eauto.
  (* The arguments have first-order inductive types. *)
  eapply PCUICFirstorder.firstorder_args in spine; eauto.
  econstructor; tea.
  - move: Hfo. rewrite /PCUICFirstorder.firstorder_ind.
    pose proof d as [[hm _] _].
    unshelve eapply PCUICTyping.declared_minductive_to_gen in hm.
    3:exact wfΣ.
    rewrite /PCUICAst.declared_minductive_gen in hm. rewrite hm.
    rewrite /PCUICFirstorder.firstorder_mutind. move/andP => [hfin _].
    now destruct ind_finite.
  - apply Forall_skipn. clear -IH spine.
    induction spine; [constructor|].
    inv IH. constructor; [|now apply IHspine].
    eapply H; tea.
Qed.

(** The hypothesis of [verified_erasure_pipeline_theorem] on the type of the
    program implies [fo_value_pars] for its value. *)
Lemma fo_value_pars_firstorder_ind (Σ : global_env_ext) t v i u args :
  PCUICTyping.wf_ext Σ ->
  PCUICTyping.typing Σ [] t (mkApps (tInd i u) args) ->
  PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i ->
  PCUICWcbvEval.eval Σ t v ->
  fo_value_pars Σ v.
Proof.
  intros wf ht fo ev.
  have hv : PCUICTyping.typing Σ [] v (mkApps (tInd i u) args).
  { eapply PCUICClassification.subject_reduction_eval; tea. }
  eapply (firstorder_value_fo_value_pars Σ (wfΣ := wf.1)); tea.
  eapply PCUICFirstorder.firstorder_value_spec; tea. apply wf. constructor.
  eapply PCUICWcbvEval.eval_to_value; tea.
Qed.

(** ** Let expansion *)

Lemma isPropositional_trans (Σ : global_env) i :
  ~~ PCUICFirstorder.isPropositional Σ i ->
  ~~ PCUICFirstorder.isPropositional
    (PCUICExpandLets.trans_global_env Σ) i.
Proof.
  move/negbTE.
  rewrite /PCUICFirstorder.isPropositional.
  rewrite /lookup_inductive /lookup_inductive_gen /lookup_minductive_gen
    PCUICExpandLetsCorrectness.trans_lookup.
  destruct lookup_env => //. destruct g => //. cbn. rewrite nth_error_mapi.
  destruct nth_error => //=.
  rewrite /PCUICFirstorder.isPropositionalArity.
  rewrite (PCUICExpandLetsCorrectness.trans_destArity []).
  destruct destArity => //.
  destruct p => //. now intros ->.
Qed.

Lemma fo_value_pars_trans (Σ : global_env_ext) v :
  PCUICTyping.wf Σ -> fo_value_pars Σ v ->
  fo_value_pars (PCUICExpandLets.trans_global Σ) (PCUICExpandLets.trans v).
Proof.
  intros wfΣ. move: v. apply: fo_value_pars_ind'.
  intros i n ui u args pandi mdecl idecl cdecl hd hty hp hf IH.
  rewrite PCUICExpandLetsCorrectness.trans_mkApps /=.
  econstructor.
  - exact (PCUICExpandLetsCorrectness.trans_declared_constructor Σ.1 _ _ _ _
      hd).
  - eapply PCUICExpandLetsCorrectness.pcuic_expand_lets in hty => //.
    2:{ now apply PCUICExpandLetsCorrectness.trans_wf. }
    rewrite !PCUICExpandLetsCorrectness.trans_mkApps in hty. exact hty.
  - now apply isPropositional_trans.
  - exact hf.
  - cbn. rewrite -map_skipn. eapply Forall_map, Forall_impl; tea.
    now intros x [].
Qed.

Lemma pcuic_lookup_inductive_pars_declared (Σ : global_env_ext) i n mdecl
  idecl cdecl :
  PCUICTyping.wf Σ -> declared_constructor Σ (i, n) mdecl idecl cdecl ->
  pcuic_lookup_inductive_pars Σ i = Some (ind_npars mdecl).
Proof.
  intros wf [[declm _] _].
  unshelve eapply PCUICTyping.declared_minductive_to_gen in declm.
  3:exact wf.
  rewrite /PCUICAst.declared_minductive_gen in declm.
  now rewrite /pcuic_lookup_inductive_pars declm.
Qed.

(** The compilation ignores parameters, the only place where let expansion
    can change a first-order value. *)
Lemma compile_value_box_trans (Σ : global_env_ext) v :
  PCUICTyping.wf Σ -> fo_value_pars Σ v ->
  compile_value_box (PCUICExpandLets.trans_global_env Σ.1)
    (PCUICExpandLets.trans v) [] =
  compile_value_box (PCUICExpandLets.trans_global_env Σ.1) v [].
Proof.
  intros wfΣ. move: v. apply: fo_value_pars_ind'.
  intros i n ui u args pandi mdecl idecl cdecl hd _ _ _ IH.
  have hnp : pcuic_lookup_inductive_pars
    (PCUICExpandLets.trans_global_env Σ.1) i = Some (ind_npars mdecl).
  { have := pcuic_lookup_inductive_pars_declared Σ i n mdecl idecl cdecl
      wfΣ hd.
    rewrite /pcuic_lookup_inductive_pars
      PCUICExpandLetsCorrectness.trans_lookup.
    destruct PCUICAst.PCUICEnvironment.lookup_env as [[]|] => //=. }
  rewrite PCUICExpandLetsCorrectness.trans_mkApps /=
    !(compile_value_box_mkApps hnp) !app_nil_r.
  f_equal. rewrite map_map !skipn_map.
  eapply map_ext_Forall, Forall_impl; tea. now intros x [].
Qed.

(** ** Erasure and the removal of parameters *)

(** The erasure of a value of [fo_value_pars] is a first-order λ□ value,
    whose parameters are lost by [ERemoveParams.strip]. *)
Lemma erases_fo_value_pars (Σ : global_env_ext) (Σer : GlobalContextMap.t)
  v :
  PCUICTyping.wf_ext Σ -> fo_value_pars Σ v ->
  erase_preserves_inductives Σ Σer ->
  forall w, Extract.erases Σ [] v w ->
  EWellformed.wellformed (efl := EWellformed.all_env_flags) Σer 0 w ->
  [/\ EFirstorder.firstorder_evalue Σer w,
    ERemoveParams.compile_evalue_box_strip Σer w [] =
      compile_value_box Σ v [] &
    ∥ EFirstorder.firstorder_ind_value Σer
        (compile_value_box Σ v []) ∥].
Proof.
  intros wf fo hpres. move: v fo.
  apply: fo_value_pars_ind'.
  intros i n ui u args pandi mdecl idecl cdecl hd hty hp hf IH w hw hwf.
  apply ErasureProperties.erases_mkApps_inv in hw
    as [(L1 & L2 & L2' & -> & [ise] & _ & _ & _)|(f' & L' & -> & hf' & hL)].
  { exfalso. eapply EArities.isErasable_Propositional in ise => //.
    now rewrite ise in hp. }
  depelim hf'.
  2:{ exfalso. eapply (EArities.isErasable_Propositional (args := [])) in X
        => //. now rewrite X in hp. }
  (* The head constructor is declared in the erased environment. *)
  rewrite (EWellformed.wellformed_mkApps (Σ := Σer)) // in hwf.
  move/andP: hwf => [hwc hwL]. cbn in hwc.
  destruct EGlobalEnv.lookup_constructor as [[[mdecl' idecl'] cdecl']|]
    eqn:hl => //.
  have hpa : EGlobalEnv.lookup_constructor_pars_args Σer i n =
    Some (EAst.ind_npars mdecl', EAst.cstr_nargs cdecl').
  { now rewrite /EGlobalEnv.lookup_constructor_pars_args hl. }
  have [enp ena] := pres_inductives_lookup Σ Σer i n mdecl idecl cdecl
    wf.1 hpres hd _ _ hpa.
  rewrite enp ena in hpa.
  have hlen : #|args| = ind_npars mdecl + cstr_arity cdecl.
  { have := PCUICInductiveInversion.Construct_Ind_ind_eq wf.1 hty hd.
    intros [[[[[_ _] _] _] hl'] _].
    rewrite hl'. f_equal.
    exact (@MetaRocq.Erasure.ErasureCorrectness.declared_constructor_arity _
      Σ.1 (i, n) mdecl idecl cdecl wf.1 hd). }
  have hlen' := Forall2_length hL.
  have hnp := pcuic_lookup_inductive_pars_declared Σ i n mdecl idecl cdecl
    wf.1 hd.
  rewrite (compile_value_box_mkApps hnp) app_nil_r.
  have hnp' : GlobalContextMap.lookup_inductive_pars Σer
    (Kernames.inductive_mind i) = Some (ind_npars mdecl).
  { rewrite GlobalContextMap.lookup_inductive_pars_spec.
    now eapply lookup_constructor_pars_args_lookup_inductive_pars. }
  rewrite (ERemoveParams.compile_evalue_box_strip_mkApps hnp') app_nil_r.
  (* Only the arguments after the parameters matter. *)
  eapply (Forall2_skipn _ _ _ _ _ (ind_npars mdecl)) in hL.
  have hwL' : forallb
    (EWellformed.wellformed (efl := EWellformed.all_env_flags) Σer 0)
    (skipn (ind_npars mdecl) L').
  { rewrite -(firstn_skipn (ind_npars mdecl) L') forallb_app in hwL.
    now move/andP: hwL => []. }
  rewrite !skipn_map.
  have IH' : Forall2 (fun a w => [/\ EFirstorder.firstorder_evalue Σer w,
      ERemoveParams.compile_evalue_box_strip Σer w [] =
        compile_value_box Σ a [] &
      ∥ EFirstorder.firstorder_ind_value Σer
        (compile_value_box Σ a []) ∥])
    (skipn (ind_npars mdecl) args) (skipn (ind_npars mdecl) L').
  { clear -IH hL hwL'. move: IH hwL'. induction hL; constructor.
    - depelim IH. destruct H0 as [_ IHx]. move/andP: hwL' => [hx _].
      now apply IHx.
    - depelim IH. move/andP: hwL' => [_ hl]. now apply IHhL. }
  clear IH hL hwL hwL'.
  split.
  - econstructor; tea; [|lia].
    clear -IH'. induction IH'; constructor; [now destruct H|exact IHIH'].
  - f_equal. clear -IH'.
    induction IH' as [|a w l l' [_ e _] _ IHl]; cbn [map] => //.
    f_equal; [exact e|exact IHl].
  - enough (∥ All (fun a => EFirstorder.firstorder_ind_value Σer
      (Basics.flip (compile_value_box Σ) [] a))
      (skipn (ind_npars mdecl) args) ∥) as [hall].
    { constructor. constructor; [|now eapply All_map].
      rewrite /EGlobalEnv.is_coind /EGlobalEnv.lookup_inductive_kind
        /EGlobalEnv.lookup_minductive.
      move: hl. rewrite /EGlobalEnv.lookup_constructor
        /EGlobalEnv.lookup_inductive /EGlobalEnv.lookup_minductive.
      destruct EGlobalEnv.lookup_env as [[|mdecl'']|] eqn:hle => //=.
      intros _.
      destruct hd as [[hm _] _].
      unshelve eapply PCUICTyping.declared_minductive_to_gen in hm.
      3:exact wf.1.
      rewrite /PCUICAst.declared_minductive_gen in hm.
      rewrite (hpres _ _ _ hle hm) /=.
      now destruct ind_finite. }
    clear -IH'. induction IH'; [constructor; constructor|].
    destruct H as [_ _ [h]]. destruct IHIH' as [hl].
    constructor. now constructor.
Qed.

(** ** The λ□ part of the pipeline *)

(** The verified λ□ part of the pipeline maps a first-order value to its
    compilation as blocks, which its readback undoes. *)
Lemma obseq_lambdabox_compile econf (p : EProgram.eprogram_env) pr p' w v' :
  obseq (verified_lambdabox_pipeline econf) p pr p' w v' ->
  EFirstorder.firstorder_evalue p.1 w ->
  EFirstorder.firstorder_ind_value p.1
    (EConstructorsAsBlocks.compile_evalue_box
      (ERemoveParams.strip p.1 w) []) ->
  v' = EConstructorsAsBlocks.compile_evalue_box
    (ERemoveParams.strip p.1 w) [] /\
  ETransform.readback (verified_lambdabox_etransform econf) v' =
    Some (ERemoveParams.strip p.1 w).
Proof.
  destruct p as [Σ t]. cbn [fst snd]. intros obs fo foi.
  pose proof pr as [[wfΣ wft] _].
  have [wfs _] := ERemoveParams.strip_program_wf
    (efl := EWellformed.all_env_flags) eq_refl eq_refl (Σ, t)
    (conj wfΣ wft).
  set (E := verified_lambdabox_etransform econf).
  have hrb : ETransform.readback E v' = Some (ERemoveParams.strip Σ w).
  { move: obs. unfold verified_lambdabox_pipeline.
    cbn [obseq compose guarded_to_unguarded_fix remove_params_optimization].
    intros [v2 [[v1 [-> ->]] obs]].
    have foq := fo_evalue_strip Σ w fo foi.
    unfold run, time in obs.
    cbn [transform compose guarded_to_unguarded_fix
      remove_params_optimization] in obs.
    unfold run, time in obs. cbn [fst] in obs.
    exact (ETransform.readback_obseq E (ERemoveParams.strip_program (Σ, t))
      _ p' (ERemoveParams.strip Σ w) v' foq obs). }
  split => //.
  apply (ETransform.readback_inj E _ _ (ERemoveParams.strip Σ w)) => //.
  rewrite lambdabox_readback.
  apply (blocks_readback_compile
    (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags)
    (EEnvMap.GlobalContextMap.make (ERemoveParams.strip_env Σ)
      (EProgram.wf_glob_fresh _ wfs))) => //.
  now apply strip_firstorder.
Qed.

(** ** The pipeline theorem *)

Section ReadbackTheorem.
  Import PCUICProgram.

  Variable Σ : global_env_ext_map.
  Variable HΣ : PCUICTyping.wf_ext Σ.
  Variable expΣ : PCUICEtaExpand.expanded_global_env Σ.1.
  Variable t : term.
  Variable expt : PCUICEtaExpand.expanded Σ.1 [] t.
  Variable Ty : term.
  Variable typing : ∥ PCUICTyping.typing Σ [] t Ty ∥.
  Variable Normalisation :
    (forall Σ, PCUICTyping.wf_ext Σ -> PCUICSN.NormalizationIn Σ).
  Variable v : term.
  Variable Heval : ∥ PCUICWcbvEval.eval Σ t v ∥.
  (** The value of [t] is a tree of constructors, with arbitrary
      parameters. *)
  Variable fov : fo_value_pars Σ v.
  Variable econf : erasure_configuration.

  Let env := PCUICExpandLets.trans_global_env Σ.

  Let Σ_t := (transform (verified_erasure_pipeline econf) (Σ, t)
    (precond _ _ _ _ expΣ expt typing _ econf)).1.
  Let t_t := (transform (verified_erasure_pipeline econf) (Σ, t)
    (precond _ _ _ _ expΣ expt typing _ econf)).2.
  Let v_t := compile_value_box env v [].

  (** The parameters and universe instances of [v], erased by the pipeline,
      are those of the expected type [T]. *)
  Variable T : term.
  Hypothesis v_at : fo_value_at env T v.

  (** The compiled program evaluates to the compilation of [v], which reads
      back to [v].

      This is compatible with axioms: unlike
      [verified_erasure_pipeline_theorem], the environment need not be
      axiom-free, as the evaluation of [t] to [v] is assumed rather than
      derived from typing by standardisation. *)
  Theorem verified_erasure_pipeline_readback :
    ∥ EWcbvEval.eval (wfl := EWcbvEvalNamed.extraction_wcbv_flags)
        Σ_t t_t v_t ∥ /\
    pipeline_readback econf env T v_t = Some v.
  Proof.
    subst Σ_t t_t.
    generalize (precond Σ t Ty HΣ expΣ expt typing Normalisation econf).
    unfold verified_erasure_pipeline.
    intros pr. destruct_compose. intros pr12.
    revert pr12. destruct_compose. intros pr1 pr2.
    cbn [transform PCUICTransform.pcuic_expand_lets_transform] in pr1, pr2 |- *.
    (* Evaluation through the three stages: let expansion, erasure and the
       λ□ part. *)
    have [v1 [ev1 e1]] := preservation
      (PCUICTransform.pcuic_expand_lets_transform _) (Σ, t) v pr Heval.
    cbn [transform obseq PCUICTransform.pcuic_expand_lets_transform]
      in ev1, e1.
    subst v1.
    have [w [ev2 hw]] := preservation erase_transform _ _ pr1 ev1.
    have [v' [ev3 obs]] :=
      preservation (verified_lambdabox_pipeline econf) _ _ pr2 ev2.
    cbn [obseq erase_transform] in hw.
    have hwf := correctness erase_transform _ pr1.
    have hpres := erase_transform_preserves_inductives _ pr1.
    pose proof (proj1 pr1) as [[wfe _]].
    have fo' : fo_value_pars (PCUICExpandLets.expand_lets_program (Σ, t)).1
      (PCUICExpandLets.trans v) :=
      fo_value_pars_trans Σ v (PCUICTyping.wf_ext_wf _ HΣ) fov.
    move: pr2 ev2 ev3 obs hwf hpres.
    generalize (transform erase_transform
      (PCUICExpandLets.expand_lets_program (Σ, t)) pr1).
    intros [Σer te] pr2 [ev2] ev3 obs [[wfg wft] _] hpres.
    cbn [fst snd] in *.
    (* The erased value [w] of [t] is first-order, with parameters that
       [strip] removes. *)
    have hww := EWcbvEval.eval_wellformed (efl := EWellformed.all_env_flags)
      Σer eq_refl wfg te w wft ev2.
    have [fow ecomp [foi]] :=
      erases_fo_value_pars _ Σer _ wfe fo' hpres w hw hww.
    have ecv : compile_value_box
      (PCUICExpandLets.expand_lets_program (Σ, t)).1
      (PCUICExpandLets.trans v) [] = v_t :=
      compile_value_box_trans Σ v (PCUICTyping.wf_ext_wf _ HΣ) fov.
    rewrite ecv in ecomp foi.
    rewrite -(compile_evalue_strip Σer w fow) in ecomp.
    rewrite -ecomp in foi.
    (* The λ□ part compiles it to [v_t], which reads back to [v]. *)
    have [ev' hrb] := obseq_lambdabox_compile econf (Σer, te) pr2 _ w v' obs
      fow foi.
    cbn [fst] in ev', hrb. subst v'.
    rewrite -ecomp. split; [exact ev3|].
    rewrite /pipeline_readback hrb /erase_readback ecomp.
    now apply readback_at_compile.
  Qed.
End ReadbackTheorem.
