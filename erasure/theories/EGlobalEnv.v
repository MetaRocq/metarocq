(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Reflect.
From MetaRocq.Erasure Require Import EAst EAstUtils ELiftSubst EReflect ECSubst.
From Stdlib Require Import ssreflect.
Import MonadNotation.

(** * Global environments

  Inductive relations for reduction, conversion and typing of CIC terms.

 *)
(** ** Environment lookup *)

Fixpoint lookup_env (Σ : global_context) id : option global_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if eq_kername id hd.1 then Some hd.2
    else lookup_env tl id
  end.

Definition declared_constant (Σ : global_context) id decl : Prop :=
  lookup_env Σ id = Some (ConstantDecl decl).

Definition declared_minductive Σ mind decl :=
  lookup_env Σ mind = Some (InductiveDecl decl).

Definition declared_inductive Σ ind mdecl decl :=
  declared_minductive Σ (inductive_mind ind) mdecl /\
  List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

Definition declared_constructor Σ cstr mdecl idecl cdecl : Prop :=
  declared_inductive Σ (fst cstr) mdecl idecl /\
  List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

Definition declared_projection Σ (proj : projection) mdecl idecl cdecl pdecl : Prop :=
  declared_constructor Σ (proj.(proj_ind), 0) mdecl idecl cdecl /\
  List.nth_error idecl.(ind_projs) proj.(proj_arg) = Some pdecl /\
  proj.(proj_npars) = ind_npars mdecl.

Lemma elookup_env_cons_fresh {kn d Σ kn'} :
  kn <> kn' ->
  EGlobalEnv.lookup_env ((kn, d) :: Σ) kn' = EGlobalEnv.lookup_env Σ kn'.
Proof.
  simpl. change (eq_kername kn' kn) with (eqb kn' kn).
  destruct (eqb_spec kn' kn). subst => //. auto.
Qed.

Section Lookups.
  Context (Σ : global_declarations).

  Definition lookup_constant kn : option constant_body :=
    decl <- lookup_env Σ kn;;
    match decl with
    | ConstantDecl cdecl => ret cdecl
    | InductiveDecl mdecl => None
    end.

  Definition lookup_minductive kn : option mutual_inductive_body :=
    decl <- lookup_env Σ kn;;
    match decl with
    | ConstantDecl _ => None
    | InductiveDecl mdecl => ret mdecl
    end.

  Definition lookup_inductive kn : option (mutual_inductive_body * one_inductive_body) :=
    mdecl <- lookup_minductive (inductive_mind kn) ;;
    idecl <- nth_error mdecl.(ind_bodies) (inductive_ind kn) ;;
    ret (mdecl, idecl).

  Definition lookup_inductive_pars kn : option nat :=
    mdecl <- lookup_minductive kn ;;
    ret mdecl.(ind_npars).

  Definition lookup_inductive_kind kn : option recursivity_kind :=
    mdecl <- lookup_minductive kn ;;
    ret mdecl.(ind_finite).

  Definition lookup_constructor kn c : option (mutual_inductive_body * one_inductive_body * constructor_body) :=
    '(mdecl, idecl) <- lookup_inductive kn ;;
    cdecl <- nth_error idecl.(ind_ctors) c ;;
    ret (mdecl, idecl, cdecl).

  Definition lookup_constructor_pars_args kn c : option (nat * nat) :=
    '(mdecl, idecl, cdecl) <- lookup_constructor kn c ;;
    ret (mdecl.(ind_npars), cdecl.(cstr_nargs)).

  Definition lookup_projection (p : projection) :
    option (mutual_inductive_body * one_inductive_body * constructor_body * projection_body) :=
    '(mdecl, idecl, cdecl) <- lookup_constructor p.(proj_ind) 0 ;;
    pdecl <- nth_error idecl.(ind_projs) p.(proj_arg) ;;
    ret (mdecl, idecl, cdecl, pdecl).

End Lookups.

Lemma declared_constant_lookup {Σ kn cdecl} :
  declared_constant Σ kn cdecl ->
  lookup_constant Σ kn = Some cdecl.
Proof.
  unfold declared_constant, lookup_constant. now intros ->.
Qed.

Lemma declared_minductive_lookup {Σ ind mdecl} :
  declared_minductive Σ ind mdecl ->
  lookup_minductive Σ ind = Some mdecl.
Proof.
  rewrite /declared_minductive /lookup_minductive.
  intros -> => /= //.
Qed.

Lemma declared_inductive_lookup {Σ ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl ->
  lookup_inductive Σ ind = Some (mdecl, idecl).
Proof.
  rewrite /declared_inductive /lookup_inductive.
  intros []. rewrite (declared_minductive_lookup H) /= H0 //.
Qed.

Lemma declared_constructor_lookup {Σ id mdecl idecl cdecl} :
  declared_constructor Σ id mdecl idecl cdecl ->
  lookup_constructor Σ id.1 id.2 = Some (mdecl, idecl, cdecl).
Proof.
  intros []. unfold lookup_constructor.
  rewrite (declared_inductive_lookup H) /= H0 //.
Qed.

Lemma declared_projection_lookup {Σ p mdecl idecl cdecl pdecl} :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  lookup_projection Σ p = Some (mdecl, idecl, cdecl, pdecl).
Proof.
  intros [hc [hp hn]]. unfold lookup_projection.
  rewrite (declared_constructor_lookup hc) /= hp //.
Qed.

(** Nested lookups *)

Lemma lookup_projection_lookup_constructor {Σ p mdecl idecl cdecl pdecl} :
  lookup_projection Σ p = Some (mdecl, idecl, cdecl, pdecl) ->
  lookup_constructor Σ p.(proj_ind) 0 = Some (mdecl, idecl, cdecl).
Proof.
  rewrite /lookup_projection; destruct lookup_constructor as [[[? ?] ?]|]=> //=.
  now destruct nth_error => //.
Qed.

Lemma lookup_constructor_lookup_inductive {Σ kn c mdecl idecl cdecl} :
  lookup_constructor Σ kn c = Some (mdecl, idecl, cdecl) ->
  lookup_inductive Σ kn = Some (mdecl, idecl).
Proof.
  rewrite /lookup_constructor; destruct lookup_inductive as [[? ?]|]=> //=.
  now destruct nth_error => //.
Qed.

(** Knowledge of propositionality status of an inductive type and parameters *)

Lemma lookup_constructor_pars_args_cstr_arity Σ ind c mdecl idecl cdecl :
  lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
  lookup_constructor_pars_args Σ ind c = Some (mdecl.(ind_npars), cdecl.(cstr_nargs)).
Proof.
  rewrite /lookup_constructor_pars_args => -> /= //.
Qed.

Definition inductive_isprop_and_pars Σ ind :=
  '(mdecl, idecl) <- lookup_inductive Σ ind ;;
  ret (idecl.(ind_propositional), mdecl.(ind_npars)).
Arguments inductive_isprop_and_pars : simpl never.

Definition constructor_isprop_pars_decl Σ ind c :=
  '(mdecl, idecl, cdecl) <- lookup_constructor Σ ind c ;;
  ret (idecl.(ind_propositional), mdecl.(ind_npars), cdecl).
Arguments constructor_isprop_pars_decl : simpl never.

Definition closed_decl (d : EAst.global_decl) :=
  match d with
  | EAst.ConstantDecl cb =>
    option_default (ELiftSubst.closedn 0) (EAst.cst_body cb) true
  | EAst.InductiveDecl _ => true
  end.

Definition closed_env (Σ : EAst.global_declarations) :=
  forallb (test_snd closed_decl) Σ.

(** Environment extension and uniqueness of declarations in well-formed global environments *)

Definition extends (Σ Σ' : global_declarations) :=
  (forall kn decl, lookup_env Σ kn = Some decl -> lookup_env Σ' kn = Some decl).

Definition extends_prefix (Σ Σ' : global_declarations) := ∑ Σ'', Σ' = Σ'' ++ Σ.

Definition fresh_global kn (Σ : global_declarations) :=
  Forall (fun x => x.1 <> kn) Σ.

Lemma lookup_env_Some_fresh {Σ c decl} :
  lookup_env Σ c = Some decl -> ~ (fresh_global c Σ).
Proof.
  induction Σ; cbn. 1: congruence.
  case: eqb_spec; intros e; subst.
  - intros [= <-] H2. inv H2.
    contradiction.
  - intros H1 H2. apply IHΣ; tas.
    now inv H2.
Qed.


(** ** Reduction *)

(** *** Helper functions for reduction *)

Definition fix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cofix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tCoFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cunfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d =>
    Some (d.(rarg), substl (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cunfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d =>
    Some (d.(rarg), substl (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition is_constructor_app_or_box t :=
  match t with
  | tBox => true
  | a =>
    let (f, a) := decompose_app a in
    match f with
    | tConstruct _ _ _ => true
    | _ => false
    end
  end.

Definition is_nth_constructor_app_or_box n ts :=
  match List.nth_error ts n with
  | Some a => is_constructor_app_or_box a
  | None => false
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

Definition iota_red npar args (br : list name * term) :=
  substl (List.rev (List.skipn npar args)) br.2.
