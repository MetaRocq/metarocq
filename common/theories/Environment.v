(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Primitive Universes.
From Equations.Prop Require Import Classes EqDecInstances.

Ltac Tauto.intuition_solver ::= auto with *.

Module Type Term.

  Parameter Inline term : Type.

  Parameter Inline tRel : nat -> term.
  Parameter Inline tSort : Sort.t -> term.
  Parameter Inline tProd : aname -> term -> term -> term.
  Parameter Inline tLambda : aname -> term -> term -> term.
  Parameter Inline tLetIn : aname -> term -> term -> term -> term.
  Parameter Inline tInd : inductive -> Instance.t -> term.
  Parameter Inline tProj : projection -> term -> term.
  Parameter Inline mkApps : term -> list term -> term.

  Parameter Inline lift : nat -> nat -> term -> term.
  Parameter Inline subst : list term -> nat -> term -> term.
  Parameter Inline closedn : nat -> term -> bool.
  Parameter Inline noccur_between : nat -> nat -> term -> bool.
  Parameter Inline subst_instance_constr : UnivSubst term.

  Notation lift0 n := (lift n 0).
End Term.

Module Type TermDecide (Import T : Term).
  #[export] Declare Instance term_eq_dec : EqDec term.
  #[export] Hint Extern 0 (ReflectEq term) => exact (@EqDec_ReflectEq term term_eq_dec) : typeclass_instances.
End TermDecide.

Module TermDecideReflectInstances (Import T : Term) (Import TDec : TermDecide T).
  #[export] Hint Extern 0 (ReflectEq term) => exact (@EqDec_ReflectEq term term_eq_dec) : typeclass_instances.
End TermDecideReflectInstances.

Module Retroknowledge.

  Record t := mk_retroknowledge {
    retro_int63 : option kername;
    retro_float64 : option kername;
    retro_string : option kername;
    retro_array : option kername;
  }.

  Definition empty := {| retro_int63 := None; retro_float64 := None; retro_string := None; retro_array := None |}.

  Definition extends (x y : t) :=
    option_extends x.(retro_int63) y.(retro_int63) /\
    option_extends x.(retro_float64) y.(retro_float64) /\
    option_extends x.(retro_string) y.(retro_string) /\
    option_extends x.(retro_array) y.(retro_array).
  Existing Class extends.

  Definition extendsb (x y : t) :=
    option_extendsb x.(retro_int63) y.(retro_int63) &&
    option_extendsb x.(retro_float64) y.(retro_float64) &&
    option_extendsb x.(retro_string) y.(retro_string) &&
    option_extendsb x.(retro_array) y.(retro_array).

  Lemma extendsT x y : reflect (extends x y) (extendsb x y).
  Proof.
    rewrite /extends/extendsb; do 4 case: option_extendsT; cbn; constructor; intuition auto.
  Qed.

  Lemma extends_spec x y : extendsb x y <-> extends x y.
  Proof.
    rewrite /extends/extendsb -!option_extends_spec /is_true !Bool.andb_true_iff //=.
    intuition auto.
  Qed.

  #[global] Instance extends_refl x : extends x x.
  Proof.
    repeat split; apply option_extends_refl.
  Qed.

  #[global] Instance extends_trans : RelationClasses.Transitive Retroknowledge.extends.
  Proof.
    intros x y z [? [? []]] [? [? []]]; repeat split; cbn; now etransitivity; tea.
  Qed.

  #[export,program] Instance reflect_t : ReflectEq t := {
      eqb x y := (x.(retro_int63) == y.(retro_int63)) &&
                 (x.(retro_float64) == y.(retro_float64)) &&
                 (x.(retro_string) == y.(retro_string)) &&
                 (x.(retro_array) == y.(retro_array))
    }.
  Next Obligation.
    do 4 case: eqb_spec; destruct x, y; cbn; intros; subst; constructor; congruence.
  Qed.

  (** This operation is asymmetric; it perfers the first argument when the arguments are incompatible, but otherwise takes the join *)
  Definition merge (r1 r2 : t) : t
    := {| retro_int63 := match r1.(retro_int63) with Some v => Some v | None => r2.(retro_int63) end
       ; retro_float64 := match r1.(retro_float64) with Some v => Some v | None => r2.(retro_float64) end
       ; retro_string := match r1.(retro_string) with Some v => Some v | None => r2.(retro_string) end
       ; retro_array := match r1.(retro_array) with Some v => Some v | None => r2.(retro_array) end
        |}.

  Lemma extends_l_merge r1 r2
    : extends r1 (merge r1 r2).
  Proof.
    rewrite /extends/merge; destruct r1, r2; cbn; repeat destruct ?; subst;
      repeat constructor; clear; destruct_head' option; constructor.
  Qed.

  Lemma extends_merge_idempotent r1 r2
    : extends r1 r2 -> merge r1 r2 = r2.
  Proof.
    rewrite /extends/merge; destruct r1, r2; cbn.
    intro; rdest; destruct_head' (@option_extends); reflexivity.
  Qed.

  Definition compatible (x y : t) : bool
    := match x.(retro_int63), y.(retro_int63) with Some x, Some y => x == y | _, _ => true end
       && match x.(retro_float64), y.(retro_float64) with Some x, Some y => x == y | _, _ => true end
       && match x.(retro_string), y.(retro_string) with Some x, Some y => x == y | _, _ => true end
       && match x.(retro_array), y.(retro_array) with Some x, Some y => x == y | _, _ => true end.

  Lemma extends_r_merge r1 r2
    : compatible r1 r2 -> extends r2 (merge r1 r2).
  Proof.
    rewrite /extends/merge/compatible; destruct r1, r2; cbn; repeat destruct ?; subst.
    all: repeat case: eqb_spec => //=.
    all: intros; subst.
    all: repeat constructor; clear; destruct_head' option; constructor.
  Qed.

End Retroknowledge.
Export (hints) Retroknowledge.

Module Environment (T : Term).

  Import T.
  #[global] Existing Instance subst_instance_constr.

  Definition judgment := judgment_ Sort.t term.

  (** ** Declarations *)
  Notation context_decl := (context_decl term).

  (** Local (de Bruijn) variable binding *)

  Definition vass x A : context_decl :=
    {| decl_name := x ; decl_body := None ; decl_type := A |}.

  (** Local (de Bruijn) let-binding *)

  Definition vdef x t A : context_decl :=
    {| decl_name := x ; decl_body := Some t ; decl_type := A |}.

  (** Local (de Bruijn) context *)

  Definition context := list context_decl.
  Definition mark_context := list relevance.
  Definition marks_of_context : context -> mark_context := fun l => List.map (fun d => d.(decl_name).(binder_relevance)) l.

  (** Last declaration first *)

  Definition lift_decl n k d := (map_decl (lift n k) d).

  Definition lift_context n k (Γ : context) : context :=
    fold_context_k (fun k' => lift n (k' + k)) Γ.

  Lemma lift_context_alt n k Γ :
    lift_context n k Γ =
    mapi (fun k' d => lift_decl n (Nat.pred #|Γ| - k' + k) d) Γ.
  Proof.
    unfold lift_context. apply: fold_context_k_alt.
  Qed.

  Lemma lift_context_length n k Γ : #|lift_context n k Γ| = #|Γ|.
  Proof. now rewrite /lift_context; len. Qed.
  #[global] Hint Rewrite lift_context_length : len.

  Definition subst_context s k (Γ : context) : context :=
    fold_context_k (fun k' => subst s (k' + k)) Γ.

  Definition subst_decl s k (d : context_decl) := map_decl (subst s k) d.

  Lemma subst_context_length s n Γ : #|subst_context s n Γ| = #|Γ|.
  Proof. now rewrite /subst_context; len. Qed.
  #[global] Hint Rewrite subst_context_length : len.

  Lemma subst_context_nil s n : subst_context s n [] = [].
  Proof. reflexivity. Qed.

  Lemma subst_context_alt s k Γ :
    subst_context s k Γ =
    mapi (fun k' d => subst_decl s (Nat.pred #|Γ| - k' + k) d) Γ.
  Proof.
    unfold subst_context, fold_context_k. rewrite rev_mapi. rewrite List.rev_involutive.
    apply mapi_ext. intros. f_equal. now rewrite List.length_rev.
  Qed.

  Lemma subst_context_snoc s k Γ d : subst_context s k (d :: Γ) = subst_context s k Γ ,, subst_decl s (#|Γ| + k) d.
  Proof.
    now rewrite /subst_context fold_context_k_snoc0.
  Qed.

  Definition subst_telescope s k (Γ : context) : context :=
    mapi (fun k' decl => map_decl (subst s (k' + k)) decl) Γ.

  Global Instance subst_instance_decl : UnivSubst context_decl
    := map_decl ∘ subst_instance.

  Global Instance subst_instance_context : UnivSubst context
    := map_context ∘ subst_instance.

  Lemma subst_instance_length u (ctx : context)
    : #|subst_instance u ctx| = #|ctx|.
  Proof. unfold subst_instance, subst_instance_context, map_context. now rewrite length_map. Qed.
  #[global] Hint Rewrite subst_instance_length : len.

  Definition set_binder_name (na : aname) (x : context_decl) : context_decl :=
    {| decl_name := na;
       decl_body := decl_body x;
       decl_type := decl_type x |}.

  (** Count the number of assumptions in a context (i.e. declarations that do not
      contain a body). *)
  Fixpoint context_assumptions (Γ : context) : nat :=
    match Γ with
    | [] => 0
    | d :: Γ =>
      match d.(decl_body) with
      | Some _ => context_assumptions Γ
      | None => S (context_assumptions Γ)
      end
    end.

  Fixpoint is_assumption_context (Γ : context) :=
    match Γ with
    | [] => true
    | d :: Γ =>
      match d.(decl_body) with
      | Some _ => false
      | None => is_assumption_context Γ
      end
    end.

  (** Smashing a context produces an assumption context. *)

  Fixpoint smash_context (Γ Γ' : context) : context :=
    match Γ' with
    | {| decl_body := Some b |} :: Γ' => smash_context (subst_context [b] 0 Γ) Γ'
    | {| decl_body := None |} as d :: Γ' => smash_context (Γ ++ [d]) Γ'
    | [] => Γ
    end.

  Lemma smash_context_length Γ Γ' : #|smash_context Γ Γ'| = #|Γ| + context_assumptions Γ'.
  Proof.
    induction Γ' as [|[na [body|] ty] tl] in Γ |- *; cbn; eauto.
    - now rewrite IHtl subst_context_length.
    - rewrite IHtl length_app. simpl. lia.
  Qed.
  #[global] Hint Rewrite smash_context_length : len.

  (* Smashing a context Γ with Δ depending on it is the same as smashing Γ
    and substituting all references to Γ in Δ by the expansions of let bindings. *)

  Lemma smash_context_app Δ Γ Γ' :
    smash_context Δ (Γ ++ Γ') = smash_context (smash_context Δ Γ) Γ'.
  Proof.
    revert Δ; induction Γ as [|[na [b|] ty]]; intros Δ; simpl; auto.
  Qed.

  Fixpoint extended_subst (Γ : context) (n : nat)
  (* Δ, smash_context Γ, n |- extended_subst Γ n : Γ *) :=
  match Γ with
  | nil => nil
  | cons d vs =>
    match decl_body d with
    | Some b =>
      (* Δ , vs |- b *)
      let s := extended_subst vs n in
      (* Δ , smash_context vs , n |- s : vs *)
      let b' := lift (context_assumptions vs + n) #|s| b in
      (* Δ, smash_context vs, n , vs |- b' *)
      let b' := subst s 0 b' in
      (* Δ, smash_context vs , n |- b' *)
      b' :: s
    | None => tRel n :: extended_subst vs (S n)
    end
  end.

  Lemma extended_subst_length Γ n : #|extended_subst Γ n| = #|Γ|.
  Proof.
    induction Γ in n |- *; simpl; auto.
    now destruct a as [? [?|] ?] => /=; simpl; rewrite IHΓ.
  Qed.
  #[global] Hint Rewrite extended_subst_length : len.

  Definition expand_lets_k Γ k t :=
    (subst (extended_subst Γ 0) k (lift (context_assumptions Γ) (k + #|Γ|) t)).

  Definition expand_lets Γ t := expand_lets_k Γ 0 t.

  Definition expand_lets_k_ctx Γ k Δ :=
    (subst_context (extended_subst Γ 0) k (lift_context (context_assumptions Γ) (k + #|Γ|) Δ)).

  Definition expand_lets_ctx Γ Δ := expand_lets_k_ctx Γ 0 Δ.

  Lemma expand_lets_k_ctx_length Γ k Δ : #|expand_lets_k_ctx Γ k Δ| = #|Δ|.
  Proof. now rewrite /expand_lets_k_ctx; len. Qed.
  #[global] Hint Rewrite expand_lets_k_ctx_length : len.

  Lemma expand_lets_ctx_length Γ Δ : #|expand_lets_ctx Γ Δ| = #|Δ|.
  Proof. now rewrite /expand_lets_ctx; len. Qed.
  #[global] Hint Rewrite expand_lets_ctx_length : len.

  Definition fix_context (m : mfixpoint term) : context :=
    List.rev (mapi (fun i d => vass d.(dname) (lift i 0 d.(dtype))) m).

  (** *** Environments *)

  (** Data associated to a single inductive constructor. *)
  Record constructor_body := {
    (** Constructor name, without the module path. *)
    cstr_name : ident;
    (** Arguments of the constructor, which can depend on the inductives in the same block
        and the parameters of the inductive : `ind_bodies ,,, ind_params |- cstr_args`. *)
    cstr_args : context;
    (** Indices of the constructor, which can depend on the inductives in the same block,
        the parameters of the inductive and the constructor arguments :
        `ind_bodies ,,, ind_params ,,, cstr_args |- cstr_indices`. *)
    cstr_indices : list term;
    (** Full type of the constructor, which can depend on the inductives in the same block :
        `ind_bodies |- cstr_type`. This should be equal to
        `forall ind_params cstr_args, I ind_params cstr_indices` *)
    cstr_type : term;
    (** Number of arguments of the constructor, _without_ let-in arguments and _without_ parameters.
        This should be equal to `context_assumptions cstr_args`. *)
    cstr_arity : nat;
  }.

  (** Data associated to a primitive projection. *)
  Record projection_body := {
    (** Projection name, without the module path. *)
    proj_name : ident;
    (** Relevance of the projection. *)
    proj_relevance : relevance;
    (** Type of the projection, wich can depend on the parameters of the inductive
        and on the object we are projecting from : `ind_params ,,, x |- proj_type`. *)
    proj_type : term;
  }.

  Definition map_constructor_body npars arities f c :=
    {| cstr_name := c.(cstr_name);
       cstr_args := fold_context_k (fun x => f (x + npars + arities)) c.(cstr_args);
       cstr_indices := map (f (npars + arities + #|c.(cstr_args)|)) c.(cstr_indices);
        (* Note only after positivity checking we can ensure that the indices do not mention the
           inductive type.. beware of lets! *)
       cstr_type := f arities c.(cstr_type);
       cstr_arity := c.(cstr_arity) |}.

  (** Here npars should be the `context_assumptions` of the parameters context. *)
  Definition map_projection_body npars f c :=
    {| proj_name := c.(proj_name);
       proj_relevance := c.(proj_relevance);
       proj_type := f (S npars) c.(proj_type)
    |}.

  (** Data associated to a single inductive in a mutual inductive block. *)
  Record one_inductive_body := {
    (** Name of the inductive, without the module path. *)
    ind_name : ident;
    (** Indices of the inductive, which can depend on the parameters :
        `ind_params |- ind_indices`. *)
    ind_indices : context;
    (** Sort of the inductive. *)
    ind_sort : Sort.t;
    (** Full type of the inductive. This should be equal to
        `forall ind_params ind_indices, tSort ind_sort` *)
    ind_type : term;
    (** Allowed eliminations for the inductive. *)
    ind_kelim : allowed_eliminations;
    (** Constructors of the inductive. Order is important. *)
    ind_ctors : list constructor_body;
    (** Names and types of primitive projections, if any. *)
    ind_projs : list projection_body;
    (** Relevance of the inductive. *)
    ind_relevance : relevance }.

  Definition map_one_inductive_body npars arities f m :=
    match m with
    | Build_one_inductive_body ind_name ind_indices ind_sort
        ind_type ind_kelim ind_ctors ind_projs ind_relevance =>
      Build_one_inductive_body
         ind_name (fold_context_k (fun x => f (npars + x)) ind_indices) ind_sort
                  (f 0 ind_type) ind_kelim (map (map_constructor_body npars arities f) ind_ctors)
                  (map (map_projection_body npars f) ind_projs) ind_relevance
    end.

  (** Data associated to a block of mutually inductive types. *)
  Record mutual_inductive_body := {
    (** Whether the block is inductive, coinductive or non-recursive (Records). *)
    ind_finite : recursivity_kind;
    (** Number of parameters (including non-uniform ones), _without_ counting let-in parameters.
        This should be equal to `context_assumptions ind_params`. *)
    ind_npars : nat;
    (** Context of parameters (including non-uniform ones), _with_ let-in parameters. *)
    ind_params : context;
    (** Components of the mutual inductive block. Order is important. *)
    ind_bodies : list one_inductive_body ;
    (** Whether the mutual inductive is universe monomorphic or universe polymorphic,
        and information about the local universes if polymorphic. *)
    ind_universes : universes_decl;
    (** Variance information. `None` when non-cumulative. *)
    ind_variance : option (list Universes.Variance.t) }.

  (** Data associated to a constant (definition, lemma or axiom). *)
  Record constant_body := {
    (** Type of the constant. *)
    cst_type : term;
    (** Body of the constant. For axioms this is [None]. *)
    cst_body : option term;
    (** Whether the constant is universe monomorphic or polymorphic, and if polymorphic
        information about its local universes. *)
    cst_universes : universes_decl;
    (** Proof relevance of this constant. *)
    cst_relevance : relevance }.

  Definition map_constant_body f decl :=
    {| cst_type := f decl.(cst_type);
       cst_body := option_map f decl.(cst_body);
       cst_universes := decl.(cst_universes);
       cst_relevance := decl.(cst_relevance) |}.

  Lemma map_cst_type f decl :
    f (cst_type decl) = cst_type (map_constant_body f decl).
  Proof. destruct decl; reflexivity. Qed.

  Lemma map_cst_body f decl :
    option_map f (cst_body decl) = cst_body (map_constant_body f decl).
  Proof. destruct decl; reflexivity. Qed.

  (** A global declaration is a definition, lemma, axiom or mutual inductive. *)
  Inductive global_decl :=
  | ConstantDecl : constant_body -> global_decl
  | InductiveDecl : mutual_inductive_body -> global_decl.
  Derive NoConfusion for global_decl.

  Definition global_declarations := list (kername * global_decl).

  Record global_env := mk_global_env
    { universes : ContextSet.t;
      declarations : global_declarations;
      retroknowledge : Retroknowledge.t }.

  Coercion universes : global_env >-> ContextSet.t.

  Definition empty_global_env :=
    {| universes := ContextSet.empty;
       declarations := [];
       retroknowledge := Retroknowledge.empty |}.

  Definition add_global_decl Σ decl :=
    {| universes := Σ.(universes);
       declarations := decl :: Σ.(declarations);
       retroknowledge := Σ.(retroknowledge) |}.

  Lemma eta_global_env Σ : Σ = {| universes := Σ.(universes); declarations := Σ.(declarations);
    retroknowledge := Σ.(retroknowledge) |}.
  Proof. now destruct Σ. Qed.

  Definition set_declarations Σ decls :=
    {| universes := Σ.(universes);
       declarations := decls;
       retroknowledge := Σ.(retroknowledge) |}.

  Fixpoint lookup_global (Σ : global_declarations) (kn : kername) : option global_decl :=
    match Σ with
    | nil => None
    | d :: tl =>
      if kn == d.1 then Some d.2
      else lookup_global tl kn
    end.

  Definition lookup_env (Σ : global_env) (kn : kername) := lookup_global Σ.(declarations) kn.

  (* version for possibly duplicative environments *)
  Fixpoint lookup_globals (Σ : global_declarations) (kn : kername) : list global_decl :=
    match Σ with
    | nil => nil
    | d :: tl =>
        let tl := lookup_globals tl kn in
        if kn == d.1 then d.2 :: tl else tl
    end.

  Definition lookup_envs (Σ : global_env) (kn : kername) := lookup_globals Σ.(declarations) kn.

  (** We define four notions of environment extension.  The two
      configurable bits are: is universe and retroknowledge extension
      strict ([Logic.eq]) or loose ([⊂_cs] / [Retroknowledge.extends]);
      and is declaration extension strict (fully order-preserving,
      i.e., new declarations are added only at the front) or lax
      (declarations may be reordered and added freely, as long as all
      new declarations with existing names come before the old ones
      with the same names, and the relative order of declarations with
      identical names is preserved).

      In most cases, we are actually interested only in duplicate-free
      environments, where the lax construction is equivalent to merely
      requiring that the lookup function agrees on all existing
      delcarations.  However, we formulate the property in a way that
      makes sense for duplicative environments so that strict
      declaration extension will always imply lax declaration
      extension.  (The lookup function prefers earlier / newer
      declarations over older ones.)

      We thus have the following implication structure:
<<<
┌-----------------------------┬------------------------┬---------------------------┐
|    univ/retro extension is: |        strict          |  lax                      |
├ declaration exension is ----┼------------------------┼---------------------------┤
|    lax                      |     extends_decls      →         extends           |
|                             |            ↑           ↗            ↑              |
|   strict                    | strictly_extends_decls → extends_strictly_on_decls |
└-----------------------------┴------------------------┴---------------------------┘
>>>
   *)
  Notation extends_decls_part_globals Σ Σ'
    := (forall c, ∑ decls, lookup_globals Σ' c = decls ++ lookup_globals Σ c)
         (only parsing).
  Notation strictly_extends_decls_part_globals Σ Σ'
    := (∑ Σ'', Σ' = Σ'' ++ Σ)
         (only parsing).
  Notation extends_decls_part Σ Σ'
    := (forall c, ∑ decls, lookup_envs Σ' c = decls ++ lookup_envs Σ c)
         (only parsing).
  Notation strictly_extends_decls_part Σ Σ'
    := (strictly_extends_decls_part_globals Σ.(declarations) Σ'.(declarations))
         (only parsing).
  Definition extends (Σ Σ' : global_env) :=
    [× Σ.(universes) ⊂_cs Σ'.(universes),
      extends_decls_part Σ Σ' &
      Retroknowledge.extends Σ.(retroknowledge) Σ'.(retroknowledge)].

  Definition extends_decls (Σ Σ' : global_env) :=
    [× Σ.(universes) = Σ'.(universes),
      extends_decls_part Σ Σ' &
      Σ.(retroknowledge) = Σ'.(retroknowledge)].

  Definition extends_strictly_on_decls (Σ Σ' : global_env) :=
    [× Σ.(universes) ⊂_cs Σ'.(universes),
      strictly_extends_decls_part Σ Σ' &
      Retroknowledge.extends Σ.(retroknowledge) Σ'.(retroknowledge)].

  Definition strictly_extends_decls (Σ Σ' : global_env) :=
    [× Σ.(universes) = Σ'.(universes),
      strictly_extends_decls_part Σ Σ' &
      Σ.(retroknowledge) = Σ'.(retroknowledge)].

  Existing Class extends.
  Existing Class extends_decls.
  Existing Class extends_strictly_on_decls.
  Existing Class strictly_extends_decls.

  Lemma lookup_global_None Σ kn : ~In kn (List.map fst Σ) <-> lookup_global Σ kn = None.
  Proof.
    move: Σ; elim => //=; try tauto.
    move => ??; case: eqb_spec; intuition congruence.
  Qed.

  Lemma hd_error_lookup_globals Σ kn : hd_error (lookup_globals Σ kn) = lookup_global Σ kn.
  Proof.
    move: Σ; elim => //= ?? <-.
    case: eqb_spec => //=.
  Qed.

  Lemma lookup_globals_nil Σ kn : ~In kn (List.map fst Σ) <-> lookup_globals Σ kn = nil.
  Proof.
    rewrite lookup_global_None-hd_error_lookup_globals.
    case: lookup_globals => //.
  Qed.

  Lemma NoDup_length_lookup_globals Σ
    : NoDup (List.map fst Σ)
      -> forall kn, List.length (lookup_globals Σ kn) = match lookup_global Σ kn with
                                                        | Some _ => 1
                                                        | None => 0
                                                        end.
  Proof.
    move => H kn.
    move: Σ H; elim => //=; try lia.
    move => ?? H. inversion 1; subst.
    move: (H ltac:(assumption)).
    case: eqb_spec => //= ->.
    rewrite (proj1 (@lookup_global_None _ _)) => //= -> //=.
  Qed.

  Lemma NoDup_lookup_globals_eq Σ
    : NoDup (List.map fst Σ)
      -> forall kn, lookup_globals Σ kn = match lookup_global Σ kn with
                                          | Some v => [v]
                                          | None => []
                                          end.
  Proof.
    move => H kn.
    move: (NoDup_length_lookup_globals Σ H kn) (hd_error_lookup_globals Σ kn).
    repeat destruct ?; subst.
    all: case: lookup_globals; cbn; try congruence.
    move => ? [|]; cbn; congruence.
  Qed.

  Lemma lookup_globals_In Σ kn decl
    : In (kn, decl) Σ <-> In decl (lookup_globals Σ kn).
  Proof.
    move: Σ; elim => //=; try tauto.
    move => [??]?; case: eqb_spec => ? //=; subst => <-; cbn in *; firstorder (subst; auto).
    all: (idtac + constructor); congruence.
  Qed.

  Lemma lookup_global_Some_if_In Σ kn decl
  : lookup_global Σ kn = Some decl -> In (kn, decl) Σ.
  Proof.
    move: Σ; elim => //=; try tauto.
    move => [??]?; case: eqb_spec => ? IH; inversion 1; subst; try rewrite <- IH by assumption.
    all: intuition try congruence; subst.
  Qed.

  Lemma lookup_global_Some_iff_In_NoDup Σ kn decl (H : NoDup (List.map fst Σ))
    : In (kn, decl) Σ <-> lookup_global Σ kn = Some decl.
  Proof.
    rewrite -hd_error_lookup_globals lookup_globals_In.
    apply NoDup_length_lookup_globals with (kn:=kn) in H; move: H.
    case: lookup_global; case: lookup_globals => [|?[]]; cbn.
    all: try lia.
    all: intuition congruence.
  Qed.

  Lemma lookup_global_extends_NoDup Σ Σ' k d :
    NoDup (List.map fst Σ') ->
    lookup_global Σ k = Some d ->
    extends_decls_part_globals Σ Σ' -> lookup_global Σ' k = Some d.
  Proof.
    rewrite /= -!hd_error_lookup_globals => Hnd.
    move: (@NoDup_length_lookup_globals _ Hnd k); clear Hnd.
    rewrite -hd_error_lookup_globals.
    move=> H Hd eq.
    move: (eq k); clear eq.
    case => ls eq.
    move: eq Hd H => ->.
    case: ls => //= ?.
    case => //=.
    case: lookup_globals => //=.
  Qed.

  Lemma lookup_env_extends_NoDup Σ Σ' k d :
    NoDup (List.map fst Σ'.(declarations)) ->
    lookup_env Σ k = Some d ->
    extends Σ Σ' -> lookup_env Σ' k = Some d.
  Proof.
    move => Hnd Hd; case => *.
    eapply lookup_global_extends_NoDup; tea.
  Qed.

  Lemma lookup_globals_app Σ Σ' kn :
    lookup_globals (Σ ++ Σ') kn = lookup_globals Σ kn ++ lookup_globals Σ' kn.
  Proof.
    move: Σ.
    elim => //= ??.
    case: eqb_spec => //= -> -> //=.
  Qed.

  Lemma strictly_extends_decls_extends_part_globals Σ Σ'
    : strictly_extends_decls_part_globals Σ Σ' -> extends_decls_part_globals Σ Σ'.
  Proof.
    case => //= ? -> c.
    rewrite lookup_globals_app.
    eexists; reflexivity.
  Qed.

  Lemma strictly_extends_decls_extends_part Σ Σ'
    : strictly_extends_decls_part Σ Σ' -> extends_decls_part Σ Σ'.
  Proof. apply strictly_extends_decls_extends_part_globals. Qed.

  #[global] Instance strictly_extends_decls_extends_decls Σ Σ' : strictly_extends_decls Σ Σ' -> extends_decls Σ Σ'.
  Proof.
    destruct Σ, Σ'; case => //= -> ? ->.
    rewrite /extends_decls; split; try reflexivity.
    now apply strictly_extends_decls_extends_part.
  Qed.

  #[global] Instance strictly_extends_decls_extends_strictly_on_decls Σ Σ' : strictly_extends_decls Σ Σ' -> extends_strictly_on_decls Σ Σ'.
  Proof.
    destruct Σ, Σ'; intros []. cbn in *; subst. split => //=.
    split; [lsets|ucsets]. apply Retroknowledge.extends_refl.
  Qed.

  #[global] Instance extends_decls_extends Σ Σ' : extends_decls Σ Σ' -> extends Σ Σ'.
  Proof.
    destruct Σ, Σ'; intros []. cbn in *; subst. split => //=.
    split; [lsets|ucsets]. apply Retroknowledge.extends_refl.
  Qed.

  #[global] Instance extends_strictly_on_decls_extends Σ Σ' : extends_strictly_on_decls Σ Σ' -> extends Σ Σ'.
  Proof.
    destruct Σ, Σ'; case => //= ? ? ?.
    rewrite /extends; split => //=.
    now apply strictly_extends_decls_extends_part.
  Qed.

  #[global] Instance strictly_extends_decls_extends_decls_subrel : CRelationClasses.subrelation strictly_extends_decls extends_decls := strictly_extends_decls_extends_decls.
  #[global] Instance strictly_extends_decls_extends_strictly_on_decls_subrel : CRelationClasses.subrelation strictly_extends_decls extends_strictly_on_decls := strictly_extends_decls_extends_strictly_on_decls.
  #[global] Instance extends_decls_extends_subrel : CRelationClasses.subrelation extends_decls extends := extends_decls_extends.
  #[global] Instance extends_strictly_on_decls_extends_subrel : CRelationClasses.subrelation extends_strictly_on_decls extends := extends_strictly_on_decls_extends.
  #[global] Instance strictly_extends_decls_extends_subrel : CRelationClasses.subrelation strictly_extends_decls extends := fun _ => _.

  #[global] Instance strictly_extends_decls_refl : CRelationClasses.Reflexive strictly_extends_decls.
  Proof. red. intros x. split => //; try exists [] => //. Qed.

  #[global] Instance extends_decls_refl : CRelationClasses.Reflexive extends_decls.
  Proof. red. intros x. split => //; try exists [] => //. Qed.

  Lemma extends_strictly_on_decls_refl : CRelationClasses.Reflexive extends_strictly_on_decls.
  Proof. red. intros x. split; [apply incl_cs_refl | try exists [] => // | apply Retroknowledge.extends_refl]. Qed.

  Lemma extends_refl : CRelationClasses.Reflexive extends.
  Proof. red. intros x. split; [apply incl_cs_refl | try exists [] => // | apply Retroknowledge.extends_refl]. Qed.

  (* easy prefers this to the local hypotheses, which is annoying
  #[global] Instance extends_refl : CRelationClasses.Reflexive extends.
  Proof. apply extends_refl. Qed.
  *)

  Lemma extends_decls_part_globals_refl Σ : extends_decls_part_globals Σ Σ.
  Proof. now exists [] => //. Qed.

  Lemma extends_decls_part_refl Σ : extends_decls_part Σ Σ.
  Proof. apply extends_decls_part_globals_refl. Qed.

  Lemma strictly_extends_decls_part_globals_refl (Σ : global_declarations)
    : strictly_extends_decls_part_globals Σ Σ.
  Proof. now exists [] => //. Qed.

  Lemma strictly_extends_decls_part_refl Σ : strictly_extends_decls_part Σ Σ.
  Proof. apply strictly_extends_decls_part_globals_refl. Qed.

  Lemma extends_decls_part_globals_trans Σ Σ' Σ''
    : extends_decls_part_globals Σ Σ' -> extends_decls_part_globals Σ' Σ'' -> extends_decls_part_globals Σ Σ''.
  Proof.
    move => H1 H2 c; move: (H1 c) (H2 c) => [? ->] [? ->].
    now eexists; rewrite app_assoc.
  Qed.

  Lemma extends_decls_part_trans Σ Σ' Σ''
    : extends_decls_part Σ Σ' -> extends_decls_part Σ' Σ'' -> extends_decls_part Σ Σ''.
  Proof. apply extends_decls_part_globals_trans. Qed.

  Lemma strictly_extends_decls_part_globals_trans (Σ Σ' Σ'' : global_declarations)
    : strictly_extends_decls_part_globals Σ Σ' -> strictly_extends_decls_part_globals Σ' Σ'' -> strictly_extends_decls_part_globals Σ Σ''.
  Proof.
    move => [? ->] [? ->].
    now eexists; rewrite app_assoc.
  Qed.

  Lemma strictly_extends_decls_part_trans Σ Σ' Σ''
    : strictly_extends_decls_part Σ Σ' -> strictly_extends_decls_part Σ' Σ'' -> strictly_extends_decls_part Σ Σ''.
  Proof. apply strictly_extends_decls_part_globals_trans. Qed.

  Local Ltac extends_trans_t :=
    intros [?] [?] [?] [?] [?]; red; cbn in *; split;
    try solve [ etransitivity; eassumption
              | eapply incl_cs_trans; eassumption
              | eapply strictly_extends_decls_part_globals_trans; eassumption
              | eapply extends_decls_part_globals_trans; eassumption ].

  #[global] Instance strictly_extends_decls_trans : CRelationClasses.Transitive strictly_extends_decls.
  Proof. extends_trans_t. Qed.
  #[global] Instance extends_decls_trans : CRelationClasses.Transitive extends_decls.
  Proof. extends_trans_t. Qed.
  #[global] Instance extends_strictly_on_decls_trans : CRelationClasses.Transitive extends_strictly_on_decls.
  Proof. extends_trans_t. Qed.
  #[global] Instance extends_trans : CRelationClasses.Transitive extends.
  Proof. extends_trans_t. Qed.

  (** Merge two lists of global_declarations, assuming that any globals sharing a name are identical *)
  Definition declared_kername_set (Σ : global_declarations) : KernameSet.t
    := List.fold_right KernameSet.add KernameSet.empty (List.map fst Σ).

  Definition merge_globals (Σ Σ' : global_declarations) : global_declarations
    := let known_kns := declared_kername_set Σ in
       List.filter (fun '(kn, _) => negb (KernameSet.mem kn known_kns)) Σ' ++ Σ.

  Definition merge_global_envs (Σ Σ' : global_env) : global_env
    := {| universes := ContextSet.union Σ.(universes) Σ'.(universes)
       ; declarations := merge_globals Σ.(declarations) Σ'.(declarations)
       ; retroknowledge := Retroknowledge.merge Σ.(retroknowledge) Σ'.(retroknowledge) |}.

  Definition compatible_globals (Σ Σ' : global_declarations) : Prop
    := forall c, lookup_globals Σ c <> [] -> lookup_globals Σ' c <> [] -> lookup_globals Σ c = lookup_globals Σ' c.

  Definition compatible (Σ Σ' : global_env)
    := Retroknowledge.compatible Σ.(retroknowledge) Σ'.(retroknowledge)
       /\ compatible_globals Σ.(declarations) Σ'.(declarations).

  Lemma lookup_globals_filter p Σ c
    : lookup_globals (filter (fun '(kn, _) => p kn) Σ) c = if p c then lookup_globals Σ c else [].
  Proof.
    induction Σ as [|?? IH]; cbn; rdest; cbn; try now repeat destruct ?.
    case: eqb_spec => ?; repeat destruct ?; subst => //=.
    all: rewrite ?eqb_refl.
    all: try case: eqb_spec => ?; subst.
    all: rewrite IH //=.
    all: try congruence.
  Qed.

  Lemma strictly_extends_decls_l_merge_globals Σ Σ'
    : strictly_extends_decls_part_globals Σ (merge_globals Σ Σ').
  Proof. now eexists. Qed.

  Lemma extends_l_merge_globals Σ Σ'
    : extends_decls_part_globals Σ (merge_globals Σ Σ').
  Proof.
    rewrite /merge_globals.
    intro c.
    rewrite lookup_globals_app lookup_globals_filter.
    eexists; reflexivity.
  Qed.

  Lemma extends_strictly_on_decls_l_merge Σ Σ'
    : extends_strictly_on_decls Σ (merge_global_envs Σ Σ').
  Proof.
    rewrite /extends_strictly_on_decls/merge_global_envs/merge_globals; cbn.
    split;
      try first [ apply ContextSet.union_spec
                | apply Retroknowledge.extends_l_merge
                | apply strictly_extends_decls_l_merge_globals ].
  Qed.
  #[export] Hint Extern 0 (extends_strictly_on_decls _ (merge_global_envs ?Σ ?Σ')) => simple apply (@extends_strictly_on_decls_l_merge Σ Σ') : typeclass_instances.

  Lemma extends_l_merge Σ Σ'
    : extends Σ (merge_global_envs Σ Σ').
  Proof. exact _. Qed.

  Lemma declared_kername_set_spec
    : forall Σ c, KernameSet.In c (declared_kername_set Σ) <-> List.In c (map fst Σ).
  Proof.
    elim => //=; try setoid_rewrite KernameSetFact.empty_iff => //=.
    move => [? ?] ? IH c //=.
    rewrite KernameSet.add_spec.
    intuition auto with *.
  Qed.

  Lemma declared_kername_set_mem_iff Σ c
    : KernameSet.mem c (declared_kername_set Σ) <-> List.In c (map fst Σ).
  Proof.
    setoid_rewrite <- KernameSetFact.mem_iff.
    apply declared_kername_set_spec.
  Qed.

  Lemma extends_r_merge_globals Σ Σ'
    : compatible_globals Σ Σ' ->
      extends_decls_part_globals Σ' (merge_globals Σ Σ').
  Proof.
    rewrite /merge_globals.
    intro H2; cbn.
    cbv [compatible_globals] in *.
    intro c.
    specialize (H2 c).
    rewrite lookup_globals_app lookup_globals_filter.
    destruct (in_dec eq_dec c (map fst Σ')) as [H'|H'];
      [ exists nil | exists (lookup_globals Σ c) ].
    2: apply lookup_globals_nil in H'; rewrite H'; clear H'.
    2: now destruct ?; cbn; rewrite app_nil_r.
    pose proof (lookup_globals_nil Σ c) as Hc.
    rewrite <- !lookup_globals_nil in H2.
    rewrite <- (declared_kername_set_mem_iff Σ) in *.
    destruct KernameSet.mem; cbn in *.
    { intuition auto. }
    { destruct Hc as [Hc _].
      rewrite Hc ?app_nil_r //=. }
  Qed.

  Lemma extends_r_merge Σ Σ'
    : compatible Σ Σ' -> extends Σ' (merge_global_envs Σ Σ').
  Proof.
    rewrite /extends/compatible/merge_global_envs/lookup_envs.
    intros [H1 H2].
    split;
      try first [ apply ContextSet.union_spec
                | now apply Retroknowledge.extends_r_merge
                | now apply extends_r_merge_globals ].
  Qed.

  Definition primitive_constant (Σ : global_env) (p : prim_tag) : option kername :=
    match p with
    | primInt => Σ.(retroknowledge).(Retroknowledge.retro_int63)
    | primFloat => Σ.(retroknowledge).(Retroknowledge.retro_float64)
    | primString => Σ.(retroknowledge).(Retroknowledge.retro_string)
    | primArray => Σ.(retroknowledge).(Retroknowledge.retro_array)
    end.

  Definition tImpl (dom codom : term) : term :=
    tProd {| binder_name := nAnon; binder_relevance := rel_of_Type |}
      dom (lift 1 0 codom).

  Definition array_uctx := ([nAnon], UnivConstraintSet.empty).

  Definition primitive_invariants (p : prim_tag) (cdecl : constant_body) :=
    match p with
    | primInt | primFloat | primString =>
     [/\ cdecl.(cst_type) = tSort Sort.type0, cdecl.(cst_body) = None &
          cdecl.(cst_universes) = Monomorphic_ctx]
    | primArray =>
      let s := sType (Universe.of_level (Level.lvar 0)) in
      [/\ cdecl.(cst_type) = tImpl (tSort s) (tSort s), cdecl.(cst_body) = None &
        cdecl.(cst_universes) = Polymorphic_ctx array_uctx]
    end.

  (** A context of global declarations + global universe constraints,
      i.e. a global environment *)

  Definition global_env_ext : Type := global_env * universes_decl.

  (** Use a coercion for this common projection of the global context. *)
  Definition fst_ctx : global_env_ext -> global_env := fst.
  Coercion fst_ctx : global_env_ext >-> global_env.

  Definition empty_ext (Σ : global_env) : global_env_ext
    := (Σ, Monomorphic_ctx).

  (** *** Programs

    A set of declarations and a term, as produced by [MetaRocq Quote Recursively]. *)

  Definition program : Type := global_env * term.

  (** Make a lambda/let-in string of abstractions from a context [Γ], ending with term [t]. *)

  Definition mkLambda_or_LetIn d t :=
    match d.(decl_body) with
    | None => tLambda d.(decl_name) d.(decl_type) t
    | Some b => tLetIn d.(decl_name) b d.(decl_type) t
    end.

  Definition it_mkLambda_or_LetIn (l : context) (t : term) :=
    List.fold_left (fun acc d => mkLambda_or_LetIn d acc) l t.

  (** Make a prod/let-in string of abstractions from a context [Γ], ending with term [t]. *)

  Definition mkProd_or_LetIn d t :=
    match d.(decl_body) with
    | None => tProd d.(decl_name) d.(decl_type) t
    | Some b => tLetIn d.(decl_name) b d.(decl_type) t
    end.

  Definition it_mkProd_or_LetIn (l : context) (t : term) :=
    List.fold_left (fun acc d => mkProd_or_LetIn d acc) l t.

  Lemma it_mkProd_or_LetIn_app l l' t :
    it_mkProd_or_LetIn (l ++ l') t = it_mkProd_or_LetIn l' (it_mkProd_or_LetIn l t).
  Proof. induction l in l', t |- *; simpl; auto. Qed.

  Fixpoint reln (l : list term) (p : nat) (Γ0 : list context_decl) {struct Γ0} : list term :=
    match Γ0 with
    | [] => l
    | {| decl_body := Some _ |} :: hyps => reln l (p + 1) hyps
    | {| decl_body := None |} :: hyps => reln (tRel p :: l) (p + 1) hyps
    end.

  Definition to_extended_list_k Γ k := reln [] k Γ.
  Definition to_extended_list Γ := to_extended_list_k Γ 0.

  Lemma reln_fold f ctx n acc :
    reln acc n (fold_context_k f ctx) =
    reln acc n ctx.
  Proof.
    induction ctx as [|[na [b|] ty] ctx] in n, acc |- *; simpl; auto;
      rewrite fold_context_k_snoc0 /=; apply IHctx.
  Qed.

  Lemma reln_list_lift_above l p Γ :
    Forall (fun x => exists n, x = tRel n /\ p <= n /\ n < p + length Γ) l ->
    Forall (fun x => exists n, x = tRel n /\ p <= n /\ n < p + length Γ) (reln l p Γ).
  Proof.
    generalize (Nat.le_refl p).
    generalize p at 1 3 5.
    induction Γ in p, l |- *. simpl. auto.
    intros. destruct a. destruct decl_body. simpl.
    assert(p0 <= S p) by lia.
    specialize (IHΓ l (S p) p0 H1). rewrite <- Nat.add_succ_comm, Nat.add_1_r.
    simpl in *. rewrite <- Nat.add_succ_comm in H0. eauto.
    simpl in *.
    specialize (IHΓ (tRel p :: l) (S p) p0 ltac:(lia)).
    rewrite <- Nat.add_succ_comm, Nat.add_1_r.
    eapply IHΓ. simpl in *. rewrite <- Nat.add_succ_comm in H0. auto.
    simpl in *.
    constructor. exists p. intuition lia. auto.
  Qed.

  Lemma to_extended_list_k_spec Γ k :
    Forall (fun x => exists n, x = tRel n /\ k <= n /\ n < k + length Γ)
           (to_extended_list_k Γ k).
  Proof.
    pose (reln_list_lift_above [] k Γ).
    unfold to_extended_list_k.
    forward f. constructor. apply f.
  Qed.

  Lemma to_extended_list_lift_above Γ :
    Forall (fun x => exists n, x = tRel n /\ n < length Γ) (to_extended_list Γ).
  Proof.
    pose (reln_list_lift_above [] 0 Γ).
    unfold to_extended_list.
    forward f. constructor. eapply Forall_impl; eauto. intros.
    destruct H; eexists; intuition eauto.
  Qed.

  Fixpoint reln_alt p (Γ : context) :=
    match Γ with
    | [] => []
    | {| decl_body := Some _ |} :: Γ => reln_alt (p + 1) Γ
    | {| decl_body := None |} :: Γ => tRel p :: reln_alt (p + 1) Γ
    end.

  Lemma reln_alt_eq l Γ k : reln l k Γ = List.rev (reln_alt k Γ) ++ l.
  Proof.
    induction Γ in l, k |- *; simpl; auto.
    destruct a as [na [body|] ty]; simpl.
    now rewrite IHΓ.
    now rewrite IHΓ -app_assoc.
  Qed.

  Lemma to_extended_list_k_cons d Γ k :
    to_extended_list_k (d :: Γ) k =
    match d.(decl_body) with
    | None => to_extended_list_k Γ (S k) ++ [tRel k]
    | Some b => to_extended_list_k Γ (S k)
    end.
  Proof.
    unfold to_extended_list_k.
    rewrite reln_alt_eq. simpl.
    destruct d as [na [body|] ty]. simpl.
    now rewrite reln_alt_eq Nat.add_1_r.
    simpl. rewrite reln_alt_eq.
    now rewrite <- app_assoc, !app_nil_r, Nat.add_1_r.
  Qed.


  Definition arities_context (l : list one_inductive_body) :=
    rev_map (fun ind => vass (mkBindAnn (nNamed ind.(ind_name))
                            rel_of_Type) ind.(ind_type)) l.

  Lemma arities_context_length l : #|arities_context l| = #|l|.
  Proof. unfold arities_context. now rewrite length_rev_map. Qed.
  #[global] Hint Rewrite arities_context_length : len.

  Lemma nth_error_arities_context idecls i idecl :
    nth_error (List.rev idecls) i = Some idecl ->
    nth_error (arities_context idecls) i =
      Some {| decl_name := {| binder_name := nNamed idecl.(ind_name); binder_relevance := rel_of_Type |};
              decl_body := None;
              decl_type := idecl.(ind_type) |}.
  Proof using Type.
    intros hnth.
    epose proof (nth_error_Some_length hnth). autorewrite with len in H.
    rewrite nth_error_rev in hnth. now autorewrite with len.
    rewrite List.rev_involutive in hnth. autorewrite with len in hnth.
    unfold arities_context.
    rewrite rev_map_spec.
    rewrite nth_error_rev; autorewrite with len; auto.
    rewrite List.rev_involutive nth_error_map.
    rewrite hnth. simpl. reflexivity.
  Qed.

  Definition map_mutual_inductive_body f m :=
    match m with
    | Build_mutual_inductive_body finite ind_npars ind_pars ind_bodies ind_universes ind_variance =>
      let arities := arities_context ind_bodies in
      let pars := fold_context_k f ind_pars in
      Build_mutual_inductive_body finite ind_npars pars
                                  (map (map_one_inductive_body (context_assumptions pars) (length arities) f) ind_bodies)
                                  ind_universes ind_variance
    end.

  Lemma ind_type_map f npars_ass arities oib :
    ind_type (map_one_inductive_body npars_ass arities f oib) = f 0 (ind_type oib).
  Proof. destruct oib. reflexivity. Qed.

  Lemma ind_ctors_map f npars_ass arities oib :
    ind_ctors (map_one_inductive_body npars_ass arities f oib) =
    map (map_constructor_body npars_ass arities f) (ind_ctors oib).
  Proof. destruct oib; simpl; reflexivity. Qed.

  Lemma ind_pars_map f m :
    ind_params (map_mutual_inductive_body f m) =
    fold_context_k f (ind_params m).
  Proof. destruct m; simpl; reflexivity. Qed.

  Lemma ind_projs_map f npars_ass arities oib :
    ind_projs (map_one_inductive_body npars_ass arities f oib) =
    map (map_projection_body npars_ass f) (ind_projs oib).
  Proof. destruct oib; simpl. reflexivity. Qed.

  Fixpoint projs ind npars k :=
    match k with
    | 0 => []
    | S k' => (tProj (mkProjection ind npars k') (tRel 0)) :: projs ind npars k'
    end.

  Lemma projs_length ind npars k : #|projs ind npars k| = k.
  Proof. induction k; simpl; auto. Qed.

  Lemma context_assumptions_fold Γ f : context_assumptions (fold_context_k f Γ) = context_assumptions Γ.
  Proof.
    rewrite fold_context_k_alt.
    unfold mapi. generalize 0 (Nat.pred #|Γ|).
    induction Γ as [|[na [body|] ty] tl]; cbn; intros; eauto.
  Qed.
  #[global] Hint Rewrite context_assumptions_fold : len.

  Lemma nth_error_fold_context_k (f : nat -> term -> term):
    forall (Γ' Γ'' : context) (v : nat),
      v < length Γ' -> forall nth,
        nth_error Γ' v = Some nth ->
        nth_error (fold_context_k f Γ') v = Some (map_decl (f (length Γ' - S v)) nth).
  Proof.
    induction Γ'; intros.
    - easy.
    - simpl. destruct v; rewrite fold_context_k_snoc0.
      + simpl. repeat f_equal; try lia. simpl in *. congruence.
      + simpl. apply IHΓ'; simpl in *; (lia || congruence).
  Qed.

  Lemma nth_error_fold_context_k_eq:
    forall (Γ' : context) (v : nat) (f : nat -> term -> term),
      nth_error (fold_context_k f Γ') v =
      option_map (map_decl (f (length Γ' - S v))) (nth_error Γ' v).
  Proof.
    induction Γ'; intros.
    - simpl. unfold fold_context_k; simpl. now rewrite nth_error_nil.
    - simpl. destruct v; rewrite fold_context_k_snoc0.
      + simpl. repeat f_equal; try lia.
      + simpl. apply IHΓ'; simpl in *; (lia || congruence).
  Qed.

  Lemma nth_error_ge {Γ Γ' v Γ''} (f : nat -> term -> term) :
    length Γ' <= v ->
    nth_error (Γ' ++ Γ) v =
    nth_error (fold_context_k f Γ' ++ Γ'' ++ Γ) (length Γ'' + v).
  Proof.
    intros Hv.
    rewrite -> !nth_error_app_ge, ?fold_context_k_length. f_equal. lia.
    rewrite fold_context_k_length. lia.
    rewrite fold_context_k_length. lia. auto.
  Qed.

  Lemma nth_error_lt {Γ Γ' Γ'' v} (f : nat -> term -> term) :
    v < length Γ' ->
    nth_error (fold_context_k f Γ' ++ Γ'' ++ Γ) v =
    option_map (map_decl (f (length Γ' - S v))) (nth_error (Γ' ++ Γ) v).
  Proof.
    simpl. intros Hv.
    rewrite -> !nth_error_app_lt.
    rewrite nth_error_fold_context_k_eq.
    do 2 f_equal. lia. now rewrite fold_context_k_length.
  Qed.

  Lemma context_assumptions_length_bound Γ : context_assumptions Γ <= #|Γ|.
  Proof.
    induction Γ; simpl; auto. destruct a as [? [?|] ?]; simpl; auto.
    lia.
  Qed.

  Lemma context_assumptions_map f Γ : context_assumptions (map_context f Γ) = context_assumptions Γ.
  Proof.
    induction Γ as [|[? [?|] ?] ?]; simpl; auto.
  Qed.

  Lemma context_assumptions_app Γ Δ : context_assumptions (Γ ++ Δ) =
    context_assumptions Γ + context_assumptions Δ.
  Proof.
    induction Γ as [|[? [] ?] ?]; simpl; auto.
  Qed.

  Lemma context_assumptions_rev Γ : context_assumptions (List.rev Γ) = context_assumptions Γ.
  Proof using Type.
    induction Γ; simpl; auto. rewrite context_assumptions_app IHΓ /=.
    destruct (decl_body a); simpl; lia.
  Qed.


  Lemma context_assumptions_mapi f Γ : context_assumptions (mapi (fun i => map_decl (f i)) Γ) =
    context_assumptions Γ.
  Proof.
    rewrite /mapi; generalize 0.
    induction Γ; simpl; intros; eauto.
    destruct a as [? [b|] ?]; simpl; auto.
  Qed.

  #[global] Hint Rewrite context_assumptions_map context_assumptions_mapi context_assumptions_app : len.

  Lemma context_assumptions_subst_instance u Γ :
    context_assumptions (subst_instance u Γ) =
    context_assumptions Γ.
  Proof. apply context_assumptions_map. Qed.

  Lemma context_assumptions_subst_context s k Γ :
    context_assumptions (subst_context s k Γ) =
    context_assumptions Γ.
  Proof. apply context_assumptions_fold. Qed.

  Lemma context_assumptions_lift_context n k Γ :
    context_assumptions (lift_context n k Γ) =
    context_assumptions Γ.
  Proof. apply context_assumptions_fold. Qed.

  #[global] Hint Rewrite context_assumptions_subst_instance
     context_assumptions_subst_context context_assumptions_lift_context : len.

  (** Lifting a relation to declarations, without alpha renaming. *)
  Inductive All_decls (P : term -> term -> Type) : context_decl -> context_decl -> Type :=
  | on_vass na t t' :
    P t t' ->
    All_decls P (vass na t) (vass na t')

  | on_vdef na b t b' t' :
    P b b' ->
    P t t' ->
    All_decls P (vdef na b t) (vdef na b' t').
  Derive Signature NoConfusion for All_decls.

  (** Allow alpha-renaming of binders *)
  Inductive All_decls_alpha (P : term -> term -> Type) : context_decl -> context_decl -> Type :=
  | on_vass_alpha na na' t t' :
    eq_binder_annot na na' ->
    P t t' ->
    All_decls_alpha P (vass na t) (vass na' t')

  | on_vdef_alpha na na' b t b' t' :
    eq_binder_annot na na' ->
    P b b' ->
    P t t' ->
    All_decls_alpha P (vdef na b t) (vdef na' b' t').
  Derive Signature NoConfusion for All_decls_alpha.

  Lemma All_decls_impl (P Q : term -> term -> Type) d d' :
    All_decls P d d' ->
    (forall t t', P t t' -> Q t t') ->
    All_decls Q d d'.
  Proof.
    intros ond H; destruct ond; constructor; auto.
  Qed.

  Lemma All_decls_alpha_impl (P Q : term -> term -> Type) d d' :
    All_decls_alpha P d d' ->
    (forall t t', P t t' -> Q t t') ->
    All_decls_alpha Q d d'.
  Proof.
    intros ond H; destruct ond; constructor; auto.
  Qed.

  Lemma All_decls_to_alpha (P : term -> term -> Type) d d' :
    All_decls P d d' ->
    All_decls_alpha P d d'.
  Proof.
    intros []; constructor; auto; reflexivity.
  Qed.

  Definition All2_fold_over (P : context -> context -> context_decl -> context_decl -> Type) Γ Γ' :=
    All2_fold (All_over P Γ Γ').

  Notation on_decls P := (fun Γ Γ' => All_decls (P Γ Γ')).
  Notation on_contexts P := (All2_fold (on_decls P)).
  Notation on_contexts_over P Γ Γ' := (All2_fold (All_over (on_decls P) Γ Γ')).

End Environment.

Module Type EnvironmentSig (T : Term).
 Include Environment T.
End EnvironmentSig.

Module Type EnvironmentDecide (T : Term) (Import E : EnvironmentSig T).
  #[export] Declare Instance context_eq_dec : EqDec context.
  #[export] Declare Instance constructor_body_eq_dec : EqDec constructor_body.
  #[export] Declare Instance projection_body_eq_dec : EqDec projection_body.
  #[export] Declare Instance one_inductive_body_eq_dec : EqDec one_inductive_body.
  #[export] Declare Instance mutual_inductive_body_eq_dec : EqDec mutual_inductive_body.
  #[export] Declare Instance constant_body_eq_dec : EqDec constant_body.
  #[export] Declare Instance global_decl_eq_dec : EqDec global_decl.
  #[export] Hint Extern 0 (ReflectEq context) => exact (@EqDec_ReflectEq context context_eq_dec) : typeclass_instances.
  #[export] Hint Extern 0 (ReflectEq constructor_body) => exact (@EqDec_ReflectEq constructor_body constructor_body_eq_dec) : typeclass_instances.
  #[export] Hint Extern 0 (ReflectEq projection_body) => exact (@EqDec_ReflectEq projection_body projection_body_eq_dec) : typeclass_instances.
  #[export] Hint Extern 0 (ReflectEq one_inductive_body) => exact (@EqDec_ReflectEq one_inductive_body one_inductive_body_eq_dec) : typeclass_instances.
  #[export] Hint Extern 0 (ReflectEq mutual_inductive_body) => exact (@EqDec_ReflectEq mutual_inductive_body mutual_inductive_body_eq_dec) : typeclass_instances.
  #[export] Hint Extern 0 (ReflectEq constant_body) => exact (@EqDec_ReflectEq constant_body constant_body_eq_dec) : typeclass_instances.
  #[export] Hint Extern 0 (ReflectEq global_decl) => exact (@EqDec_ReflectEq global_decl global_decl_eq_dec) : typeclass_instances.
End EnvironmentDecide.

Module EnvironmentDecideReflectInstances (T : Term) (Import E : EnvironmentSig T) (Import EDec : EnvironmentDecide T E).
  #[export] Hint Extern 0 (ReflectEq context) => exact (@EqDec_ReflectEq context context_eq_dec) : typeclass_instances.
  #[export] Hint Extern 0 (ReflectEq constructor_body) => exact (@EqDec_ReflectEq constructor_body constructor_body_eq_dec) : typeclass_instances.
  #[export] Hint Extern 0 (ReflectEq projection_body) => exact (@EqDec_ReflectEq projection_body projection_body_eq_dec) : typeclass_instances.
  #[export] Hint Extern 0 (ReflectEq one_inductive_body) => exact (@EqDec_ReflectEq one_inductive_body one_inductive_body_eq_dec) : typeclass_instances.
  #[export] Hint Extern 0 (ReflectEq mutual_inductive_body) => exact (@EqDec_ReflectEq mutual_inductive_body mutual_inductive_body_eq_dec) : typeclass_instances.
  #[export] Hint Extern 0 (ReflectEq constant_body) => exact (@EqDec_ReflectEq constant_body constant_body_eq_dec) : typeclass_instances.
  #[export] Hint Extern 0 (ReflectEq global_decl) => exact (@EqDec_ReflectEq global_decl global_decl_eq_dec) : typeclass_instances.
End EnvironmentDecideReflectInstances.

Module Type TermUtils (T: Term) (E: EnvironmentSig T).
  Import T E.

  Parameter Inline destArity : context -> term -> option (context × Sort.t).
  Parameter Inline inds : kername -> Instance.t -> list one_inductive_body -> list term.

End TermUtils.
