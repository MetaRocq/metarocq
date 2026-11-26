(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure Require Import EAst EAstUtils EGlobalEnv EWellformed EEnvMap EInduction
  ELiftSubst EProgram.

(** * Checking the well-formedness of erased programs

    Boolean decision procedure for [wf_eprogram]. To avoid linear lookups in the environment,
    well-formedness is checked using environment maps ([GlobalContextMap.t]), built
    incrementally from the oldest declaration. *)

Section WfMap.
  Context {efl : EEnvFlags} (Σ : GlobalContextMap.t).

  Definition wf_brs_map ind brsl :=
    match GlobalContextMap.lookup_inductive Σ ind with
    | Some (mib, oib) => #|oib.(ind_ctors)| == brsl
    | None => false
    end.

  (** [wellformed], using the lookup functions of the environment map *)
  Fixpoint wellformed_map k (t : term) : bool :=
    match t with
    | tRel i => has_tRel && Nat.ltb i k
    | tEvar ev args => has_tEvar && List.forallb (wellformed_map k) args
    | tLambda _ M => has_tLambda && wellformed_map (S k) M
    | tApp u v => has_tApp && wellformed_map k u && wellformed_map k v
    | tLetIn na b b' => has_tLetIn && wellformed_map k b && wellformed_map (S k) b'
    | tCase ind c brs => has_tCase &&
      let brs' := List.forallb (fun br => wellformed_map (#|br.1| + k) br.2) brs in
      wf_brs_map ind.1 #|brs| && wellformed_map k c && brs'
    | tProj p c => has_tProj && isSome (GlobalContextMap.lookup_projection Σ p) && wellformed_map k c
    | tFix mfix idx => has_tFix &&
      List.forallb (fun d => isLambda d.(dbody) || has_tLazy_Force && EAstUtils.isLazy d.(dbody)) mfix &&
      wf_fix_gen wellformed_map k mfix idx
    | tCoFix mfix idx => has_tCoFix &&
      List.forallb (fun d => EAst.isLambdas d.(rarg) d.(dbody)) mfix &&
      wf_fix_gen wellformed_map k mfix idx
    | tBox => has_tBox
    | tConst kn => has_tConst &&
      match GlobalContextMap.lookup_constant Σ kn with
      | Some d => has_axioms || isSome d.(cst_body)
      | _ => false
      end
    | tConstruct ind c block_args => has_tConstruct &&
      isSome (GlobalContextMap.lookup_constructor Σ ind c) &&
      if cstr_as_blocks then match GlobalContextMap.lookup_constructor_pars_args Σ ind c with
        | Some (p, a) => (p + a) == #|block_args|
        | _ => true end
        && forallb (wellformed_map k) block_args else is_nil block_args
    | tVar _ => has_tVar
    | tPrim p => has_prim p && EPrimitive.test_prim (wellformed_map k) p
    | tLazy t => has_tLazy_Force && wellformed_map k t
    | tForce t => has_tLazy_Force && wellformed_map k t
    end.

  Definition wf_global_decl_map d : bool :=
    match d with
    | ConstantDecl cb => option_default (fun b => wellformed_map 0 b) cb.(cst_body) has_axioms
    | InductiveDecl idecl => wf_minductive idecl
    end.

End WfMap.

Lemma wellformed_map_spec {efl : EEnvFlags} (Σ : GlobalContextMap.t) k t :
  wellformed_map Σ k t = wellformed Σ k t.
Proof.
  induction t in k |- * using EInduction.term_forall_list_ind; cbn;
    rewrite ?GlobalContextMap.lookup_env_spec
      ?GlobalContextMap.lookup_projection_spec ?GlobalContextMap.lookup_constant_spec
      ?GlobalContextMap.lookup_constructor_spec ?GlobalContextMap.lookup_constructor_pars_args_spec;
    unfold wf_brs_map, wf_brs; rewrite ?GlobalContextMap.lookup_inductive_spec;
    rewrite ?IHt ?IHt1 ?IHt2 ?IHt3 //.
  all: try solve [f_equal; solve_all].
  all: try (unfold wf_fix_gen; do 2 f_equal; solve_all).
  - destruct cstr_as_blocks => //. f_equal. solve_all.
Qed.

Lemma wf_global_decl_map_spec {efl : EEnvFlags} (Σ : GlobalContextMap.t) d :
  wf_global_decl_map Σ d = wf_global_decl Σ d.
Proof.
  destruct d as [[[]]|] => //=. apply wellformed_map_spec.
Qed.

Lemma lookup_env_None_fresh Σ kn :
  EGlobalEnv.lookup_env Σ kn = None -> EGlobalEnv.fresh_global kn Σ.
Proof.
  induction Σ as [|[kn' d] Σ IH]; cbn; constructor.
  - cbn. case: (ReflectEq.eqb_spec kn kn') H => // hneq _. congruence.
  - apply IH. now destruct ReflectEq.eqb.
Qed.

Lemma lookup_env_map_None_fresh (Σ : GlobalContextMap.t) kn :
  GlobalContextMap.lookup_env Σ kn = None -> EGlobalEnv.fresh_global kn Σ.
Proof.
  rewrite GlobalContextMap.lookup_env_spec. apply lookup_env_None_fresh.
Qed.

Definition option_None_dec {A} (o : option A) : {o = None} + {o <> None} :=
  match o return {o = None} + {o <> None} with
  | None => left eq_refl
  | Some a => right (fun h : Some a = None =>
      match h in _ = y return match y with None => False | Some _ => True end with eq_refl => I end)
  end.

(** Returns the environment map of [Σ] if it is well-formed *)
Fixpoint check_wf_glob {efl : EEnvFlags} (Σ : global_declarations) : option GlobalContextMap.t :=
  match Σ with
  | [] => Some GlobalContextMap.empty
  | (kn, d) :: Σ =>
    match check_wf_glob Σ with
    | None => None
    | Some m =>
      match option_None_dec (GlobalContextMap.lookup_env m kn) with
      | left hl =>
        if wf_global_decl_map m d then
          Some (GlobalContextMap.add m kn d (lookup_env_map_None_fresh m kn hl))
        else None
      | right _ => None
      end
    end
  end.

Definition check_wf_eprogram (efl : EEnvFlags) (p : eprogram) : bool :=
  match @check_wf_glob efl (fst p) with
  | Some m => @wellformed_map efl m 0 (snd p)
  | None => false
  end.

Lemma check_wf_glob_spec {efl : EEnvFlags} Σ m :
  check_wf_glob Σ = Some m -> wf_glob Σ /\ GlobalContextMap.global_decls m = Σ.
Proof.
  induction Σ as [|[kn d] Σ IH] in m |- *; cbn.
  - intros [= <-]. split => //. constructor.
  - destruct (check_wf_glob Σ) as [m'|] => //.
    specialize (IH _ eq_refl) as [wfΣ heq].
    destruct option_None_dec as [hl|] => //.
    destruct wf_global_decl_map eqn:hd => //. intros [= <-]. cbn.
    rewrite wf_global_decl_map_spec heq in hd. split; [|now rewrite heq].
    constructor => //. rewrite -heq. now apply lookup_env_map_None_fresh.
Qed.

Lemma check_wf_eprogram_spec efl p : check_wf_eprogram efl p -> wf_eprogram efl p.
Proof.
  unfold check_wf_eprogram.
  destruct check_wf_glob as [m|] eqn:hm => // ht.
  apply check_wf_glob_spec in hm as [wfΣ heq].
  rewrite wellformed_map_spec heq in ht. now split.
Qed.

Lemma fresh_global_lookup_env_None kn Σ :
  EGlobalEnv.fresh_global kn Σ -> EGlobalEnv.lookup_env Σ kn = None.
Proof.
  induction 1 as [|[kn' d] Σ hneq _ IH]; cbn => //.
  case: (ReflectEq.eqb_spec kn kn') => // heq. subst. now elim hneq.
Qed.

Lemma check_wf_glob_complete {efl : EEnvFlags} Σ :
  wf_glob Σ -> exists m, check_wf_glob Σ = Some m /\ GlobalContextMap.global_decls m = Σ.
Proof.
  induction 1 as [|kn d Σ wfΣ [m [hm heq]] hd hfresh]; cbn.
  - now eexists.
  - rewrite hm.
    destruct option_None_dec as [hl|hl].
    + rewrite wf_global_decl_map_spec heq hd. eexists; split; [reflexivity|]. cbn. now rewrite heq.
    + elim hl. rewrite GlobalContextMap.lookup_env_spec heq.
      now apply fresh_global_lookup_env_None.
Qed.

Lemma check_wf_eprogram_complete efl p : wf_eprogram efl p -> check_wf_eprogram efl p.
Proof.
  intros [wfΣ ht]. unfold check_wf_eprogram.
  destruct (check_wf_glob_complete _ wfΣ) as [m [-> heq]].
  now rewrite wellformed_map_spec heq.
Qed.
