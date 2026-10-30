(** * Eta-expansion and proof generation **)

(** We perform eta-expansion of template-rocq terms and generate proofs that
    we terms are equal to the originals. Since eta-conversion is part of the
    Rocq's conversion, the proof is essentially [eq_refl].
    All dependencies are also expanded.*)
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import String.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Template Require Import All.
From MetaRocq.Erasure.Typed Require Import Erasure.
From MetaRocq.Erasure.Typed Require Import Optimize.
From MetaRocq.Erasure.Typed Require Import Utils.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Erasure.Typed Require Import Extraction.
From MetaRocq.Erasure.Typed Require Import Certifying.

Open Scope nat.
Import MonadNotation.

Section Eta.
  Definition ctors_info := list (inductive
                                 * nat (* constructor number *)
                                 * nat (* how much to expand *)
                                 * term (* constructor's type *)
                                ).
  Definition constansts_info := list (kername * nat * term).

  Context (ctors : ctors_info).
  Context (constants : constansts_info).
  Context (Σ : global_env).

  Fixpoint remove_top_prod (t : Ast.term) (n : nat) :=
    match n,t with
    | O, _ => t
    | S m, tProd nm ty1 ty2 => remove_top_prod ty2 m
    | _, _ => t
    end.

  (** Eta-expands the given term of the form [(t args)].

      [Γ] -- context used to specialise the type of the term along with the arguments [args];
             particularly useful for eta-expanding constructors -- contains the list of inductives the constructor belongs to;
      [t] -- a term;
      [args] -- arguments to which the term is applied;
      [ty] -- the term's type;
      [count] -- how much to expand *)
  Definition eta_single (Γ : list term)
                        (t : Ast.term)
                        (args : list Ast.term)
                        (ty : Ast.term)
                        (count : nat)
                        : term :=
    let needed := count - #|args| in
    let prev_args := map (lift0 needed) args in
    let eta_args := rev_map tRel (seq 0 needed) in
    let cut_ty := remove_top_prod ty #|args| in
    (* NOTE: we substitute the arguments and the context Γ in order to "specialise" the term's type *)
    let subst_ty := subst (rev args ++ rev Γ ) 0 cut_ty in
    let remaining := firstn needed (decompose_prod subst_ty).1.2 in
    let remaining_names := firstn needed (decompose_prod subst_ty).1.1 in
    fold_right (fun '(nm,ty) b => Ast.tLambda nm ty b) (mkApps t (prev_args ++ eta_args)) (combine remaining_names remaining).


  Record ind_info :=
    { ind_info_inductive : inductive;
      ind_info_nmind : nat (* how many mutual inductives in the definition *)
    }.

  Definition eta_ctor (ind_i : ind_info) (c : nat)
           (u : Instance.t)
           (args : list term) : term :=
    let ind := ind_i.(ind_info_inductive) in
    match find (fun '(ind', c', _, _) => eq_inductive ind' ind && (c' =? c)) ctors with
    | Some (_, _,n,ty) =>
      let ind := mkInd ind.(inductive_mind) ind.(inductive_ind) in
      let Γind := map
                    (fun i => tInd (mkInd ind.(inductive_mind) i) [])
                    (seq 0 (ind_i.(ind_info_nmind))) in
      eta_single Γind (Ast.tConstruct ind c u) args ty n
    | None => mkApps (tConstruct ind c u) args
    end.

Definition eta_const (kn : kername) (u : Instance.t) (args : list term) : term :=
  match find (fun '(kn',n, _) => eq_kername kn' kn) constants with
  | Some (_, n, ty) => eta_single [] (tConst kn u) args ty n
  | None => mkApps (tConst kn u) args
  end.

Definition get_ind_info (ind : inductive) : option ind_info :=
   match lookup_env Σ ind.(inductive_mind) with
      | Some (InductiveDecl mib) =>
        let n_mind := mib.(ind_bodies) in
        Some {| ind_info_inductive := ind; ind_info_nmind := #|n_mind| |}
      | _ => None
   end.

(** We assume that all applications are "flattened" e.g. of the form
    [tApp hd [t1; t2; t3; ...; tn]] where hd itself is not an application.
    This is guaranteed for quoted terms. *)
Fixpoint eta_expand (t : term) : term :=
  match t with
  | tApp hd args =>
    match hd with
    | tConstruct ind c u =>
      match get_ind_info ind with
      | Some ind_i => eta_ctor ind_i c u (map eta_expand args)
      | _ => tVar ("Error: lookup of an inductive failed for "
                    ++ string_of_kername ind.(inductive_mind))
      end

    | tConst kn u => eta_const kn u (map eta_expand args)
    | _ => mkApps (eta_expand hd) (map eta_expand args)
    end
  | tEvar n ts => tEvar n (map eta_expand ts)
  | tLambda na ty body => tLambda na ty (eta_expand body)
  | tLetIn na val ty body => tLetIn na (eta_expand val) ty (eta_expand body)
  | tCase p pr disc brs =>
    tCase p pr (eta_expand disc) (map (map_branch eta_expand) brs)
  | tProj p t => tProj p (eta_expand t)
  | tFix def i => tFix (map (map_def id eta_expand) def) i
  | tCoFix def i => tCoFix (map (map_def id eta_expand) def) i
  (* NOTE: we know that constructors and constants are not applied at this point,
     since applications are captured by the previous cases *)
  | tConstruct ind c u =>
    match get_ind_info ind with
    | Some ind_i => eta_ctor ind_i c u (map eta_expand [])
    | None => tVar ("Error: lookup of an inductive failed for "
                     ++ string_of_kername ind.(inductive_mind))
    end
  | tConst kn u => eta_const kn u (map eta_expand [])
  | t => t
  end.

End Eta.

Definition from_oib (ds : dearg_set) (kn : kername) (ind_index : nat) (oib : one_inductive_body) : ctors_info :=
  let f i '(Build_constructor_body _ _ _ ty _) :=
      let ind := mkInd kn ind_index in
      let mm := get_mib_masks ds.(ind_masks) kn in
      match mm with
      | Some m =>
        let cm := get_ctor_mask ds.(ind_masks) ind i in
        Some (ind,i,#|cm|,ty)
      | None => None
      end in
  fold_lefti (fun i acc c => match f i c with Some v => v :: acc| None => acc end)
             0 oib.(ind_ctors) [].

Fixpoint get_eta_info (Σ : global_declarations) (ds : dearg_set) : ctors_info * constansts_info :=
  match Σ with
  | (kn, InductiveDecl mib) :: Σ' =>
    let '(ctors, consts) := get_eta_info Σ' ds in
    (List.concat (mapi (from_oib ds kn) mib.(ind_bodies)) ++ ctors, consts)%list
  | (kn, ConstantDecl cb) :: Σ' =>
    let '(ctors, consts) := get_eta_info Σ' ds in
    (ctors, (kn, #|get_const_mask ds.(const_masks) kn|, cb.(cst_type)) :: consts)
  | [] => ([],[])
  end.


Definition restrict_env (Σ : global_declarations) (kns : list kername) : global_declarations :=
  filter (fun '(kn, _) => match find (eq_kername kn) kns with
                       | Some _ => true
                       | None => false
                       end) Σ.

Import PCUICWfEnv PCUICWfEnvImpl.

Lemma eq_eta_global_env (cf := config.extraction_checker_flags) Σ' Σ :
  abstract_env_rel (abstract_env_impl := (@optimized_abstract_env_impl config.extraction_checker_flags fake_guard_impl_instance).π1) (build_wf_env_from_env (cf := config.extraction_checker_flags) Σ' (assume_env_wellformed Σ')) Σ ->
  Σ =
  {|
    PEnv.universes := PEnv.universes Σ';
    PEnv.declarations := PEnv.declarations Σ';
    PEnv.retroknowledge := PEnv.retroknowledge Σ'
  |}.
Proof.
  cbn. intros ->. now destruct Σ'.
Qed.

Definition eta_global_env
           (overridden_masks : kername -> option bitmask)
           (trim_consts trim_inds : bool)
           (Σ : global_env)
           (seeds : KernameSet.t)
           (erasure_ignore : kername -> bool) :=
  let Σp := PCUICProgram.trans_env_env (TemplateToPCUIC.trans_global_env Σ) in
  let Σe :=
      erase_global_decls_deps_recursive
        (X_type := optimized_abstract_env_impl (guard := fake_guard_impl_instance))
        (X := build_wf_env_from_env Σp (assume_env_wellformed _))
        (PEnv.declarations Σp) (PEnv.universes Σp) (PEnv.retroknowledge Σp) (eq_eta_global_env _)
        seeds erasure_ignore in
  let (const_masks, ind_masks) := analyze_env overridden_masks Σe in
  let const_masks := (if trim_consts then trim_const_masks else id) const_masks in
  let ind_masks := (if trim_inds then trim_ind_masks else id) ind_masks in
  let f cb :=
      match cb.(cst_body) with
      | Some b => let (ctors, consts) := get_eta_info (declarations Σ) {| ind_masks := ind_masks;
                                                           const_masks := const_masks |} in
                  {| cst_type := cb.(cst_type);
                     cst_body := Some (eta_expand ctors consts Σ b);
                     cst_universes := cb.(cst_universes);
                     cst_relevance := cb.(cst_relevance)|}
      | None => cb
      end in
  let Σ' := restrict_env (declarations Σ) (map (fun '(kn, _, _) => kn) Σe) in
  map_constants_global_env id f {| universes := universes Σ; declarations := Σ'; retroknowledge := retroknowledge Σ |}.

Definition eta_global_env_template
           (overridden_masks : kername -> option bitmask)
           (trim_consts trim_inds : bool)
           (mpath : modpath)
           (Σ : global_env)
           (seeds : KernameSet.t) (erasure_ignore : kername -> bool)
  : TemplateMonad global_env :=
  let suffix := "_expanded" in
  Σext <- tmEval lazy (eta_global_env overridden_masks trim_consts trim_inds Σ seeds erasure_ignore);;
  gen_defs_and_proofs (declarations Σ) (declarations Σext) mpath suffix seeds;;
  ret Σext.

(** Mainly for testing purposes *)

(* Needs to set universe to Set otherwise make vos without Universe Checking fails *)
Definition extract_def_name {A : Type} (a : A) : TemplateMonad@{_ Set} KernameSet.elt :=
  extract_def_name a.

Definition eta_expand_def
           {A}
           (overridden_masks : kername -> option bitmask)
           (trim_inds trim_consts : bool) (def : A) : TemplateMonad _ :=
  cur_mod <- tmCurrentModPath tt;;
  p <- tmQuoteRecTransp def false ;;
  kn <- extract_def_name def ;;
  eta_global_env_template
    overridden_masks trim_inds trim_consts cur_mod p.1
    (KernameSet.singleton kn) (fun _ => false).

Definition template_eta
           (overriden_masks : kername -> option bitmask)
           (trim_consts trim_inds : bool)
           (seeds : list kername)
           (erasure_ignore : kername -> bool)
  : Transform.TemplateTransform :=
  let seeds := KernameSetProp.of_list seeds in
  fun Σ => Ok (Utils.timed "Eta-expand"
                        (fun _ => eta_global_env overriden_masks
                                              trim_consts
                                              trim_inds
                                              Σ
                                              seeds
                                              erasure_ignore)).

(*Module Examples.

  Module Ex1.
  Definition partial_app_pair :=
    let p : forall B : Type, unit -> B -> unit × B := @pair unit in
    p bool tt true.
  End Ex1.
  MetaRocq Quote Recursively Definition p_app_pair_syn := Ex1.partial_app_pair.

  Module Test1.
    MetaRocq Run (cur_mod <- tmCurrentModPath tt;;
                 eta_global_env_template
                  (fun _ => None)
                   false false cur_mod
                   p_app_pair_syn.1
                   (KernameSet.singleton <%% Ex1.partial_app_pair %%>)
                   (fun _ => false)).
  End Test1.


  Inductive MyInd (A B C : Type) :=
    miCtor : A * A -> B -> C -> True -> MyInd A B C.

  Module Ex2.
    Definition partial_app1 A B n m := let f := miCtor A in f B bool (let n' := @pair A in n' A n n) m true I.
    Definition partial_app2 := let f := partial_app1 in f bool true.
  End Ex2.

  Set Printing Implicit.
  (** Expands the dependencies and adds the corresponding definitions *)
  MetaRocq Run (eta_expand_def
                 (fun _ => None)
                 true true
                 Ex2.partial_app2).

  (** [partial_app2_expanded] is defined in terms of [partial_app1_expanded] *)
  (* FIXME: it's a bit fragile to refer to unquoted definitions, because their names depend on a module/path they are in *)
  (* Print MetaRocq.Erasure.Typed_CertifyingEta_Examples_Ex2_partial_app2_expanded. *)
  (* MetaRocq.Erasure.Typed_CertifyingEta_Examples_Ex2_partial_app2_expanded =
  let f :=
    fun A B : Type => MetaRocq.Erasure.Typed_CertifyingEta_Examples_Ex2_partial_app1_expanded A B in
  f bool true
       : bool -> true -> MyInd bool true bool
   *)

  Inductive MyInd1 (A B C : Type) :=
    | miCtor0 : MyInd1 A B C
    | miCtor1 : A * A -> B -> True -> C -> MyInd1 A B C.

  Definition partial_app3 A B n m :=
    let f := miCtor1 A in f B bool n m I.

  MetaRocq Run (eta_expand_def (fun _ => None) true true partial_app3).

  Module Ex3.
  Definition inc_balance (st : nat × nat) (new_balance : nat)
                 (p : (0 <=? new_balance) = true) :=
    (st.1 + new_balance, st.2).

  Definition partial_inc_balance st i := inc_balance st i.
  End Ex3.
  MetaRocq Run (cur_mod <- tmCurrentModPath tt;;
               p <- tmQuoteRecTransp Ex3.partial_inc_balance false ;;
               eta_global_env_template
                 (fun _ => None)
                 true true
                 cur_mod
                 p.1
                 (KernameSet.singleton <%% Ex3.partial_inc_balance %%>)
                 (fun _ => false)
              ).

  Module Ex4.
    (** Partially applied constructor of a recursive inductive type *)
    Definition papp_cons A (x : A) (xs : list A) := let my_cons := @cons in
                                                      my_cons A x xs.

    MetaRocq Run (eta_expand_def (fun _ => None) false false papp_cons).
  End Ex4.

  Module Ex5.

    (** Mutual inductive *)
    Inductive even : nat -> Type :=
    | even_O : even 0
    | even_S : forall n, odd n -> even (S n)
    with odd : nat -> Type :=
    | odd_S : forall n, even n -> odd (S n).

    Definition papp_odd :=
      let f := odd_S 0 in
      f even_O.

    MetaRocq Run (eta_expand_def (fun _ => None) false false papp_odd).

    Inductive Expr (Annot : Type) :=
    | eNat : nat -> Expr Annot
    | eFn : string -> Expr Annot -> Expr Annot
    | eAnnot : Annot -> Expr Annot
    | eApp : Expr Annot -> Exprs Annot -> Expr Annot
    with Exprs (Annot : Type) :=
    | eNil : Exprs Annot
    | eCons : Expr Annot -> Exprs Annot -> Exprs Annot.

    Definition papp_expr :=
      let part_app := eApp _ (eFn unit "f" (eNat unit 0)) in
      part_app (eCons _ (eNat unit 0) (eNil _)).

    MetaRocq Run (eta_expand_def (fun _ => None) false false papp_expr).
  End Ex5.

End Examples.
*)
