From Stdlib Require Import Utf8 Program.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv EWellformed EWcbvEval.
From MetaRocq.Utils Require Import bytestring MRString.
From MetaRocq.Erasure Require Import EWcbvEvalCstrsAsBlocksFixLambdaInd.
From Stdlib Require Import Relations.Relations.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.
Set Default Proof Using "Type*".

Axiom eval_case_unfold_constr :
  ∀ (wfl : WcbvFlags) Σ mfix idx args nargs fn v,
  cunfold_cofix mfix idx = Some (nargs, fn) -> 
  eval Σ (mkApps fn args) v ->
  isConstructApp v ∨ isBox v.

(* 
  Autre possibilité:
  rajouter une règle d'évaluation des cofix qui se comporte bien + transformation axiomatisée pour passer d'une règle à l'autre et changer les flags
*)

Section eval_cofix_ind_dep.
  Context {wfl : WcbvFlags} {Σ : global_context} (P : ∀ x y : term, eval Σ x y -> Type).
  Variable f_box :
    ∀ (a t t' : term) (e : eval Σ a tBox), 
    P a tBox e -> 
    ∀ e0 : eval Σ t t', 
    P t t' e0 -> 
    P (tApp a t) tBox (eval_box Σ a t t' e e0).

  Variable f_beta : 
    ∀ (f0 : term) (na : name) (b a a' res : term) (e : eval Σ f0 (tLambda na b)),
    P f0 (tLambda na b) e -> 
    ∀ e0 : eval Σ a a', P a a' e0 -> 
    ∀ e1 : eval Σ (csubst a' 0 b) res, 
    P (csubst a' 0 b) res e1 -> 
    P (tApp f0 a) res (eval_beta Σ f0 na b a a' res e e0 e1).

  Variable f_zeta :
    ∀ (na : name) (b0 b0' b1 res : term) (e : eval Σ b0 b0'),
    P b0 b0' e ->
    ∀ e0 : eval Σ (csubst b0' 0 b1) res, 
    P (csubst b0' 0 b1) res e0 -> 
    P (tLetIn na b0 b1) res (eval_zeta Σ na b0 b0' b1 res e e0).

  Variable f_iota : 
    ∀ (ind : inductive) (pars : nat) (cdecl : constructor_body) 
      (discr : term) (c : nat) (args : list term) (brs : list (list name × term)) 
      (br : list name × term) (res : term)
      (e : with_constructor_as_block = false) 
      (e0 : eval Σ discr (mkApps (tConstruct ind c []) args)),
    P discr (mkApps (tConstruct ind c []) args) e0 -> 
    ∀ (e1 : constructor_isprop_pars_decl Σ ind c = Some (false, pars, cdecl))
      (e2 : nth_error brs c = Some br)
      (e3 : #|args| = pars + cstr_nargs cdecl) 
      (e4 : #|skipn pars args| = #|br.1|)
      (e5 : eval Σ (iota_red pars args br) res),
    P (iota_red pars args br) res e5 ->
    P (tCase (ind, pars) discr brs) res (eval_iota Σ ind pars cdecl discr c args brs br res e e0 e1 e2 e3 e4 e5).

  Variable f_iota_block :
    ∀ (ind : inductive) (pars : nat) (cdecl : constructor_body) 
      (discr : term) (c : nat) (args : list term) (brs : list (list name × term)) 
      (br : list name × term) (res : term) 
      (e : with_constructor_as_block = true) 
      (e0 : eval Σ discr (tConstruct ind c args)),
    P discr (tConstruct ind c args) e0 -> 
    ∀ (e1 : constructor_isprop_pars_decl Σ ind c = Some (false, pars, cdecl)) 
      (e2 : nth_error brs c = Some br) 
      (e3 : #|args| = pars + cstr_nargs cdecl) 
      (e4 : #|skipn pars args| = #|br.1|) 
      (e5 : eval Σ (iota_red pars args br) res), 
    P (iota_red pars args br) res e5 -> 
    P (tCase (ind, pars) discr brs) res (eval_iota_block Σ ind pars cdecl discr c args brs br res e e0 e1 e2 e3 e4 e5).

  Variable f_iota_sing :
    ∀ (ind : inductive) (pars : nat) (discr : term) (brs : list (list name × term)) 
      (n : list name) (f4 res : term) (i : with_prop_case) (e : eval Σ discr tBox), 
    P discr tBox e -> 
    ∀ (e0 : inductive_isprop_and_pars Σ ind = Some (true, pars)) 
      (e1 : brs = [(n, f4)]) (e2 : eval Σ (substl (repeat tBox #|n|) f4) res),
    P (substl (repeat tBox #|n|) f4) res e2 -> 
    P (tCase (ind, pars) discr brs) res (eval_iota_sing Σ ind pars discr brs n f4 res i e e0 e1 e2).

  Variable f_fix :
    ∀ (f5 : term) (mfix : mfixpoint term) (idx : nat) (argsv : list term) 
      (a av fn res : term) (guarded : with_guarded_fix) 
      (e : eval Σ f5 (mkApps (tFix mfix idx) argsv)), 
    P f5 (mkApps (tFix mfix idx) argsv) e -> 
    ∀ e0 : eval Σ a av,
    P a av e0 -> 
    ∀ (e1 : cunfold_fix mfix idx = Some (#|argsv|, fn)) 
      (e2 : eval Σ (tApp (mkApps fn argsv) av) res),
    P (tApp (mkApps fn argsv) av) res e2 ->
    P (tApp f5 a) res (eval_fix Σ f5 mfix idx argsv a av fn res guarded e e0 e1 e2).
  
  Variable f_fix_value :
    ∀ (f6 : term) (mfix : mfixpoint term) (idx : nat) (argsv : list term) 
      (a av : term) (narg : nat) (fn : term) (guarded : with_guarded_fix) 
      (e : eval Σ f6 (mkApps (tFix mfix idx) argsv)),
    P f6 (mkApps (tFix mfix idx) argsv) e ->
    ∀ e0 : eval Σ a av,
    P a av e0 -> 
    ∀ (e1 : cunfold_fix mfix idx = Some (narg, fn)) (l : #|argsv| < narg),
    P (tApp f6 a) (tApp (mkApps (tFix mfix idx) argsv) av) (eval_fix_value Σ f6 mfix idx argsv a av narg fn guarded e e0 e1 l).
    
  Variable f_fix' :
    ∀ (f7 : term) (mfix : mfixpoint term) (idx : nat) 
      (a av fn res : term) (narg : nat) 
      (unguarded : with_guarded_fix = false) 
      (e : eval Σ f7 (tFix mfix idx)), 
    P f7 (tFix mfix idx) e ->
    ∀ (e0 : cunfold_fix mfix idx = Some (narg, fn)) (e1 : eval Σ a av), 
    P a av e1 -> ∀ e2 : eval Σ (tApp fn av) res, P (tApp fn av) res e2 ->
    P (tApp f7 a) res (eval_fix' Σ f7 mfix idx a av fn res narg unguarded e e0 e1 e2).

  Variable f_cofix_case_no_cstr_as_blocks :
    ∀ discr mfix idx args nargs fn ind c con_args
      npars0 cdecl brs br res
      (cstr_blocks : with_constructor_as_block = false)
      (e : eval Σ discr (mkApps (tCoFix mfix idx) args))
      (e0 : cunfold_cofix mfix idx = Some (nargs, fn))
      (e1 : eval Σ (mkApps fn args) (mkApps (tConstruct ind c []) con_args))
      (e2 : constructor_isprop_pars_decl Σ ind c = Some (false, npars0, cdecl))
      (e3 : nth_error brs c = Some br)
      (e4 : #|con_args| = npars0 + cstr_nargs cdecl)
      (e5 : #|skipn npars0 con_args| = #|br.1|)
      (e6 : eval Σ (iota_red npars0 con_args br) res),
      P _ _ e ->
      P _ _ e1 ->
      P _ _ e6 ->
      P (tCase (ind, npars0) discr brs) res 
        (eval_cofix_case _ _ _ _ _ _ _ _ _ _ e e0 
          (eval_iota _ _ _ _ _ _ _ _ _ _ cstr_blocks e1 e2 e3 e4 e5 e6)).

  Variable f_cofix_case_cstr_as_blocks :
    ∀ discr mfix idx args nargs fn ind c con_args
      npars0 cdecl brs br res
      (cstr_blocks : with_constructor_as_block)
      (e : eval Σ discr (mkApps (tCoFix mfix idx) args))
      (e0 : cunfold_cofix mfix idx = Some (nargs, fn))
      (e1 : eval Σ (mkApps fn args) (tConstruct ind c con_args))
      (e2 : constructor_isprop_pars_decl Σ ind c = Some (false, npars0, cdecl))
      (e3 : nth_error brs c = Some br)
      (e4 : #|con_args| = npars0 + cstr_nargs cdecl)
      (e5 : #|skipn npars0 con_args| = #|br.1|)
      (e6 : eval Σ (iota_red npars0 con_args br) res),
      P _ _ e ->
      P _ _ e1 ->
      P _ _ e6 ->
      P (tCase (ind, npars0) discr brs) res 
        (eval_cofix_case _ _ _ _ _ _ _ _ _ _ e e0 
          (eval_iota_block _ _ _ _ _ _ _ _ _ _ cstr_blocks e1 e2 e3 e4 e5 e6)).
  
  Variable f_cofix_case_prop :
    ∀ discr mfix idx args nargs fn ind
      npars brs n f res
      (prop_case : with_prop_case)
      (e : eval Σ discr (mkApps (tCoFix mfix idx) args))
      (e0 : cunfold_cofix mfix idx = Some (nargs, fn))
      (e1 : eval Σ (mkApps fn args) tBox)
      (e2 : inductive_isprop_and_pars Σ ind = Some (true, npars))
      (e3 : brs = [(n, f)])
      (e4 : eval Σ (substl (repeat tBox #|n|) f) res),
      P _ _ e ->
      P _ _ e1 ->
      P _ _ e4 ->
      P (tCase (ind, npars) discr brs) res 
        (eval_cofix_case _ _ _ _ _ _ _ _ _ _ e e0 
          (eval_iota_sing _ _ _ _ _ _ _ _ prop_case e1 e2 e3 e4)).

  Variable f_cofix_proj_no_cstr_as_blocks :
    ∀ discr mfix idx args nargs fn p con_args cdecl a res
      (cstr_blocks : with_constructor_as_block = false)
      (e : eval Σ discr (mkApps (tCoFix mfix idx) args))
      (e0 : cunfold_cofix mfix idx = Some (nargs, fn))
      (e1 : eval Σ (mkApps fn args) (mkApps (tConstruct (proj_ind p) 0 []) con_args))
      (e2 : constructor_isprop_pars_decl Σ (proj_ind p) 0 = Some (false, proj_npars p, cdecl))
      (e3 : #|con_args| = proj_npars p + cstr_nargs cdecl)
      (e4 : nth_error con_args (proj_npars p + proj_arg p) = Some a )
      (e5 : eval Σ a res),
      P _ _ e ->
      P _ _ e1 ->
      P _ _ e5 ->
      P (tProj p discr) res 
        (eval_cofix_proj _ _ _ _ _ _ _ _ _ e e0 
          (eval_proj _ _ _ _ _ _ _ cstr_blocks e1 e2 e3 e4 e5)).

  Variable f_cofix_proj_cstr_as_blocks :
    ∀ discr mfix idx args nargs fn p con_args cdecl a res
      (cstr_blocks : with_constructor_as_block)
      (e : eval Σ discr (mkApps (tCoFix mfix idx) args))
      (e0 : cunfold_cofix mfix idx = Some (nargs, fn))
      (e1 : eval Σ (mkApps fn args) (tConstruct (proj_ind p) 0 con_args))
      (e2 : constructor_isprop_pars_decl Σ (proj_ind p) 0 = Some (false, proj_npars p, cdecl))
      (e3 : #|con_args| = proj_npars p + cstr_nargs cdecl)
      (e4 : nth_error con_args (proj_npars p + proj_arg p) = Some a )
      (e5 : eval Σ a res),
      P _ _ e ->
      P _ _ e1 ->
      P _ _ e5 ->
      P (tProj p discr) res 
        (eval_cofix_proj _ _ _ _ _ _ _ _ _ e e0 
          (eval_proj_block _ _ _ _ _ _ _ cstr_blocks e1 e2 e3 e4 e5)).

  Variable f_cofix_proj_prop :
    ∀ discr mfix idx args nargs fn p
      (prop_case : with_prop_case)
      (e : eval Σ discr (mkApps (tCoFix mfix idx) args))
      (e0 : cunfold_cofix mfix idx = Some (nargs, fn))
      (e1 : eval Σ (mkApps fn args) tBox)
      (e2 : inductive_isprop_and_pars Σ (proj_ind p) = Some (true, proj_npars p)),
      P _ _ e ->
      P _ _ e1 ->
      P (tProj p discr) tBox 
        (eval_cofix_proj _ _ _ _ _ _ _ _ _ e e0 
          (eval_proj_prop _ _ _ prop_case e1 e2)).

  Variable f_delta :
    ∀ (c : kername) (decl : constant_body) (body : term) 
      (isdecl : declared_constant Σ c decl) (res : term)
      (e : cst_body decl = Some body) (e0 : eval Σ body res),
    P body res e0 ->
    P (tConst c) res (eval_delta Σ c decl body isdecl res e e0).

  Variable f_proj :
    ∀ (p : projection) (cdecl : constructor_body) (discr : term) (args : list term) 
      (a res : term) (e : with_constructor_as_block = false) 
      (e0 : eval Σ discr (mkApps (tConstruct (proj_ind p) 0 []) args)),
    P discr (mkApps (tConstruct (proj_ind p) 0 []) args) e0 ->
    ∀ (e1 : constructor_isprop_pars_decl Σ (proj_ind p) 0 = Some (false, proj_npars p, cdecl)) 
      (e2 : #|args| = proj_npars p + cstr_nargs cdecl) 
      (e3 : nth_error args (proj_npars p + proj_arg p) = Some a) 
      (e4 : eval Σ a res), 
    P a res e4 -> 
    P (tProj p discr) res (eval_proj Σ p cdecl discr args a res e e0 e1 e2 e3 e4).
  
  Variable f_proj_block :
    ∀ (p : projection) (cdecl : constructor_body) (discr : term) 
      (args : list term) (a res : term) 
      (e : with_constructor_as_block = true) 
      (e0 : eval Σ discr (tConstruct (proj_ind p) 0 args)),
    P discr (tConstruct (proj_ind p) 0 args) e0 ->
    ∀ (e1 : constructor_isprop_pars_decl Σ (proj_ind p) 0 = Some (false, proj_npars p, cdecl)) 
      (e2 : #|args| = proj_npars p + cstr_nargs cdecl) 
      (e3 : nth_error args (proj_npars p + proj_arg p) = Some a) 
      (e4 : eval Σ a res),
    P a res e4 ->
    P (tProj p discr) res (eval_proj_block Σ p cdecl discr args a res e e0 e1 e2 e3 e4).

  Variable f_proj_prop :
    ∀ (p : projection) (discr : term) (i : with_prop_case) 
      (e : eval Σ discr tBox), 
    P discr tBox e -> 
    ∀ e0 : inductive_isprop_and_pars Σ (proj_ind p) = Some (true, proj_npars p),
    P (tProj p discr) tBox (eval_proj_prop Σ p discr i e e0).

  Variable f_construct :
    ∀ (ind : inductive) (c : nat) (mdecl : mutual_inductive_body) 
      (idecl : one_inductive_body) (cdecl : constructor_body) (f14 : term) 
      (args : list term) (a a' : term)
      (e : with_constructor_as_block = false)
      (e0 : lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl))
      (e1 : eval Σ f14 (mkApps (tConstruct ind c []) args)),
      P f14 (mkApps (tConstruct ind c []) args) e1 -> 
      ∀ (l : #|args| < cstr_arity mdecl cdecl) (e2 : eval Σ a a'),
      P a a' e2 -> 
      P (tApp f14 a) (tApp (mkApps (tConstruct ind c []) args) a')
        (eval_construct Σ ind c mdecl idecl cdecl f14 args a a' e e0 e1 l e2).

  Variable f_construct_block :
    ∀ (ind : inductive) (c : nat) (mdecl : mutual_inductive_body) 
      (idecl : one_inductive_body) (cdecl : constructor_body) (args args' : list term) 
      (e : with_constructor_as_block = true) 
      (e0 : lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl))
      (e1 : #|args| = cstr_arity mdecl cdecl) (a : All2_Set (eval Σ) args args'), 
    All2_over a P ->
    P (tConstruct ind c args) (tConstruct ind c args') 
      (eval_construct_block Σ ind c mdecl idecl cdecl args args' e e0 e1 a).

  Variable f_app_cong :
    ∀ (f16 f' a a' : term) (e : eval Σ f16 f'),
    P f16 f' e -> 
    ∀ (i : ~~ (
            isLambda f' || 
            (if with_guarded_fix then isFixApp f' else isFix f') ||
            isBox f' ||
            isConstructApp f' ||
            isPrimApp f' ||
            isLazyApp f'
          )
      ) 
      (e0 : eval Σ a a'),
    P a a' e0 -> 
    P (tApp f16 a) (tApp f' a') (eval_app_cong Σ f16 f' a a' e i e0).

  Variable f_prim :
    ∀ (p p' : prim_val term) (ev : eval_primitive (eval Σ) p p'),
    eval_primitive_ind (eval Σ) P p p' ev -> P (tPrim p) (tPrim p') (eval_prim Σ p p' ev).

  Variable f_force :
    ∀ (t t' v : term) (ev1 : eval Σ t (tLazy t')) (ev2 : eval Σ t' v),
    P t (tLazy t') ev1 ->
    P t' v ev2 ->
    P (tForce t) v (eval_force Σ t t' v ev1 ev2).

  Variable f_atom :
    ∀ (t : term) (i : atom Σ t), 
    P t t (eval_atom Σ t i).

  Fixpoint eval_cofix_ind_dep : ∀ x y e, P x y e.
  Proof.
    intros t1 t2.
    destruct e.
    - now apply f_box.
    - now apply f_beta.
    - now apply f_zeta.
    - now apply f_iota.
    - now apply f_iota_block.
    - now apply f_iota_sing. 
    - now apply f_fix.
    - now apply f_fix_value.
    - now apply f_fix'.
    - depelim e3.
      + now apply f_cofix_case_no_cstr_as_blocks.
      + now apply f_cofix_case_cstr_as_blocks.
      + now apply f_cofix_case_prop.
      + exfalso.
        eapply eval_case_unfold_constr in e3_1 as [h | h]; last easy.
        * now rewrite /isConstructApp head_mkApps in h.
        * pose proof (nisBox_mkApps (tCoFix mfix0 idx0) args0) eq_refl as h'.
          now rewrite h in h'.
      + exfalso. easy.
    - depelim e3.
      + exfalso.
        eapply eval_case_unfold_constr in e3_1 as [h | h]; last easy.
        * now rewrite /isConstructApp head_mkApps in h.
        * pose proof (nisBox_mkApps (tCoFix mfix0 idx0) args0) eq_refl as h'.
          now rewrite h in h'.
      + now apply f_cofix_proj_no_cstr_as_blocks.
      + now apply f_cofix_proj_cstr_as_blocks.
      + now apply f_cofix_proj_prop.
      + exfalso. easy.
    - now apply f_delta.
    - now apply f_proj.
    - now apply f_proj_block.
    - now apply f_proj_prop.
    - now apply f_construct.
    - apply f_construct_block.
      clear e e0 e1.
      now induction a; constructor.
    - now apply f_app_cong.
    - apply f_prim.
      depelim e; constructor.
      + clear a a'.
        now induction ev; constructor.
      + easy.
    - now apply f_force.
    - now apply f_atom.
  Qed.
End eval_cofix_ind_dep.

From MetaRocq.Erasure.StepIndex Require Import Utils SubstLemmas.

Section eval_cofix_ind.
  Context {wfl : WcbvFlags} {efl : EEnvFlags} {Σ : global_context} (wf_Σ : wf_glob Σ) 
          (h_app : has_tApp) (no_prop_case : ~~ with_prop_case) (no_guarded_fix : ~~ with_guarded_fix)
          (no_cstr_params : ~~ has_cstr_params) (cstr_blocks : cstr_as_blocks) (cstr_blocks' : with_constructor_as_block).
  Context (P : ∀ x y : term, Type).
  Variable f_box :
    ∀ (a t t' : term), 
    eval Σ a tBox ->
    P a tBox -> 
    eval Σ t t' ->
    P t t' -> 
    P (tApp a t) tBox.

  Variable f_beta : 
    ∀ (f0 : term) (na : name) (b a a' res : term),
    eval Σ f0 (tLambda na b) ->
    P f0 (tLambda na b) -> 
    eval Σ a a' ->
    P a a' -> 
    eval Σ (csubst a' 0 b) res ->
    P (csubst a' 0 b) res -> 
    P (tApp f0 a) res.

  Variable f_zeta :
    ∀ (na : name) (b0 b0' b1 res : term),
    eval Σ b0 b0' ->
    P b0 b0' ->
    eval Σ (csubst b0' 0 b1) res ->
    P (csubst b0' 0 b1) res -> 
    P (tLetIn na b0 b1) res.

  Variable f_iota_block :
    ∀ (ind : inductive) (pars : nat) (cdecl : constructor_body) 
      (discr : term) (c : nat) (args : list term) (brs : list (list name × term)) 
      (br : list name × term) (res : term),
    with_constructor_as_block ->
    eval Σ discr (tConstruct ind c args) ->
    P discr (tConstruct ind c args) -> 
    constructor_isprop_pars_decl Σ ind c = Some (false, pars, cdecl) ->
    nth_error brs c = Some br ->
    #|args| = pars + cstr_nargs cdecl ->
    #|skipn pars args| = #|br.1| ->
    eval Σ (iota_red pars args br) res ->
    P (iota_red pars args br) res -> 
    P (tCase (ind, pars) discr brs) res.

  Variable f_fix' :
    ∀ (f5 : term) (mfix : mfixpoint term) (idx : nat) (a av : term)
      (fn : term) na d res,
    with_guarded_fix = false ->
    eval Σ f5 (tFix mfix idx) ->
    P f5 (tFix mfix idx) ->
    nth_error mfix idx = Some d ->
    d.(dbody) = tLambda na fn ->
    eval Σ a av -> 
    P a av -> 
    eval Σ (substl (av :: fix_subst mfix) fn) res ->
    P (substl (av :: fix_subst mfix) fn) res ->
    P (tApp f5 a) res.

  Variable f_cofix_case :
    ∀ discr mfix idx args nargs fn ind c con_args
      npars0 cdecl brs br res,
      with_constructor_as_block ->
      eval Σ discr (mkApps (tCoFix mfix idx) args) ->
      P discr (mkApps (tCoFix mfix idx) args) ->
      EGlobalEnv.cunfold_cofix mfix idx = Some (nargs, fn) ->
      eval Σ (mkApps fn args) (tConstruct ind c con_args) ->
      P (mkApps fn args) (tConstruct ind c con_args) ->
      constructor_isprop_pars_decl Σ ind c = Some (false, npars0, cdecl) ->
      nth_error brs c = Some br ->
      #|con_args| = npars0 + cstr_nargs cdecl ->
      #|skipn npars0 con_args| = #|br.1| ->
      eval Σ (iota_red npars0 con_args br) res ->
      P (iota_red npars0 con_args br) res ->
      P (tCase (ind, npars0) discr brs) res.

  Variable f_cofix_proj :
    ∀ discr mfix idx args nargs fn p con_args cdecl a res,
      with_constructor_as_block ->
      eval Σ discr (mkApps (tCoFix mfix idx) args) ->
      P discr (mkApps (tCoFix mfix idx) args) ->
      EGlobalEnv.cunfold_cofix mfix idx = Some (nargs, fn) ->
      eval Σ (mkApps fn args) (tConstruct (proj_ind p) 0 con_args) ->
      P (mkApps fn args) (tConstruct (proj_ind p) 0 con_args) ->
      constructor_isprop_pars_decl Σ (proj_ind p) 0 = Some (false, proj_npars p, cdecl) ->
      #|con_args| = proj_npars p + cstr_nargs cdecl ->
      nth_error con_args (proj_npars p + proj_arg p) = Some a  ->
      eval Σ a res ->
      P a res ->
      P (tProj p discr) res.

  Variable f_delta :
    ∀ (c : kername) (decl : constant_body) (body : term) (res : term),
    declared_constant Σ c decl ->
    cst_body decl = Some body ->
    eval Σ body res ->
    P body res ->
    P (tConst c) res.

  Variable f_proj_block :
    ∀ (p : projection) (cdecl : constructor_body) (discr : term) (args : list term) (a res : term),
    with_constructor_as_block ->
    eval Σ discr (tConstruct (proj_ind p) 0 args) ->
    P discr (tConstruct (proj_ind p) 0 args) ->
    constructor_isprop_pars_decl Σ (proj_ind p) 0 = Some (false, proj_npars p, cdecl) ->
    #|args| = proj_npars p + cstr_nargs cdecl ->
    nth_error args (proj_npars p + proj_arg p) = Some a ->
    eval Σ a res ->
    P a res ->
    P (tProj p discr) res.

  Variable f_construct_block :
    ∀ (ind : inductive) (c : nat) (mdecl : mutual_inductive_body) 
      (idecl : one_inductive_body) (cdecl : constructor_body) (args args' : list term),
    with_constructor_as_block ->
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    #|args| = cstr_arity mdecl cdecl ->
    All2 (eval Σ) args args' -> 
    All2 P args args' ->
    P (tConstruct ind c args) (tConstruct ind c args').

  Variable f_app_cong :
    ∀ (f16 f' a a' : term),
    eval Σ f16 f' ->
    P f16 f' -> 
    ~~ (isLambda f' || (if with_guarded_fix then isFixApp f' else isFix f') ||
        isBox f' || isConstructApp f' || isPrimApp f' || isLazyApp f' ) ->
    eval Σ a a' ->
    P a a' -> 
    P (tApp f16 a) (tApp f' a').
  
  Variable f_prim :
    ∀ (p p' : prim_val term) (ev : eval_primitive (eval Σ) p p'),
    eval_primitive_ind (eval Σ) (λ x y _, P x y) p p' ev -> 
    P (tPrim p) (tPrim p').

  Variable f_force :
    ∀ (t t' v : term),
    eval Σ t (tLazy t') -> 
    eval Σ t' v ->
    P t (tLazy t') ->
    P t' v ->
    P (tForce t) v.

  Variable f_atom :
    ∀ (t : term),
    atom Σ t -> 
    P t t.

  Fixpoint eval_cofix_ind :
    ∀ x y (e : eval Σ x y),
    wellformed Σ 0 x ->
    P x y.
  Proof.
    intros t1 t2 e wf_x.
    destruct e.
    - eapply f_box; try easy.
      + now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x.
      + now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x.
    - eapply f_beta; try easy.
      { now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x. }
      { now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x. }
      eapply eval_cofix_ind; try easy.
      rewrite /= !andb_and in wf_x.
      apply eval_wellformed in e1; try easy.
      apply eval_wellformed in e2; try easy.
      rewrite /= !andb_and in e1, e2.
      now apply wellformed_csubst.
    - eapply f_zeta; try easy.
      { now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x. }
      eapply eval_cofix_ind; try easy.
      rewrite /= !andb_and in wf_x.
      apply eval_wellformed in e1; try easy.
      now apply wellformed_csubst.
    - now exfalso.
    - eapply f_iota_block; try easy.
      { now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x. }
      eapply eval_cofix_ind; try easy.
      rewrite /= /wf_brs !andb_and in wf_x.
      apply eval_wellformed in e2; try easy.
      eapply wellformed_iota_red; try easy.
      + rewrite /= !andb_and in e2.
        destruct cstr_as_blocks.
        * now rewrite /= !andb_and in e2.
        * now destruct args.
      + destruct wf_x as (? & ? & wf_brs).
        eapply nth_error_forallb in wf_brs; try easy.
        now rewrite Nat.add_0_r in wf_brs.
    - exfalso. now destruct with_prop_case.
    - exfalso. now destruct with_guarded_fix.
    - exfalso. now destruct with_guarded_fix.
    - unfold EGlobalEnv.cunfold_fix in e2.
      destruct (nth_error mfix idx) eqn:heq; last easy.
      assert (isLambda (dbody d)).
      { rewrite /= !andb_and in wf_x.
        apply eval_wellformed in e1 as wf_tFix; try easy.
        rewrite /= !andb_and in wf_tFix.
        now eapply @nth_error_forallb with (p := λ d, isLambda (dbody d)). }
      destruct d as [? [] ?]; try easy.
      injection e2 as ? ?; subst.
      rewrite substl_substlg0 substlg_tLambda in e4.
      depelim e4; try solve[ easy |
        depelim e4_1; simpl in *; try easy;
        apply (f_equal head) in H0;
        now rewrite head_mkApps in H0
      ].
      assert (av = a').
      { eapply eval_value; last eassumption.
        now eapply eval_to_value.  }
      apply eval_value in e4_1 as heq'; last now do 2 constructor.
      injection heq' as ? ?; subst.
      assert (eval Σ (substl (a' :: fix_subst mfix) t) res).
      { rewrite -substlg_csubst_commute in e4_3; try easy.
        - rewrite /= !andb_and in wf_x.
          apply eval_wellformed in e3; simpl in *; try easy.
          now eapply wellformed_closed.
        - rewrite /= !andb_and in wf_x.
          apply closed_fix_subst.
          apply eval_wellformed in e1; try easy.
          rewrite /= !andb_and in e1.
          eapply forallb_impl; last easy.
          intros. now eapply wellformed_closed. }
      eapply f_fix'; try easy.
      { now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x. }
      { now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x. }
      eapply eval_cofix_ind; first assumption.
      rewrite /= !andb_and in wf_x.
      eapply wellformed_substl.
      + simpl. rewrite andb_and; split.
        * now apply eval_wellformed in e3.
        * apply eval_wellformed in e1; try easy.
          rewrite /= !andb_and in e1.
          now apply wellformed_fix_subst.
      + simpl. rewrite fix_subst_length.
        apply eval_wellformed in e1; try easy.
        rewrite /= !andb_and in e1.
        eapply nth_error_forallb in heq; try easy.
        rewrite /= !andb_and in heq.
        apply heq.
    - depelim e3.
      + now exfalso.
      + assert (wellformed Σ 0 (mkApps fn args)).
        { rewrite /= !andb_and in wf_x.
          apply eval_wellformed in e1; try easy.
          rewrite wellformed_mkApps //= !andb_and in e1.
          rewrite wellformed_mkApps // !andb_and.
          split; last easy.
          eapply wellformed_cunfold_cofix; try easy.
          now rewrite /= !andb_and. }
        eapply f_cofix_case; try easy.
        { now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x. }
        eapply eval_cofix_ind; try easy.
        rewrite /= /wf_brs !andb_and in wf_x.
        apply eval_wellformed in e3_1; try easy.
        rewrite /= cstr_blocks !andb_and in e3_1.
        eapply wellformed_iota_red; try easy.
        rewrite -(Nat.add_0_r #|_|).
        now eapply nth_error_forallb in e3; last easy.
      + exfalso. now destruct with_prop_case.
      + exfalso.
        eapply eval_case_unfold_constr in e3_1 as [h | h]; last easy.
        * now rewrite /isConstructApp head_mkApps in h.
        * pose proof (nisBox_mkApps (tCoFix mfix0 idx0) args0) eq_refl as h'.
          now rewrite h in h'.
      + now exfalso.
    - depelim e3.
      + exfalso.
        eapply eval_case_unfold_constr in e3_1 as [h | h]; last easy.
        * now rewrite /isConstructApp head_mkApps in h.
        * pose proof (nisBox_mkApps (tCoFix mfix0 idx0) args0) eq_refl as h'.
          now rewrite h in h'.
      + now exfalso.
      + assert (wellformed Σ 0 (mkApps fn args)).
        { rewrite /= !andb_and in wf_x.
          apply eval_wellformed in e1; try easy.
          rewrite wellformed_mkApps //= !andb_and in e1.
          rewrite wellformed_mkApps // !andb_and.
          split; last easy.
          eapply wellformed_cunfold_cofix; try easy.
          now rewrite /= !andb_and. }
        eapply f_cofix_proj; try easy.
        { now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x. }
        eapply eval_cofix_ind; try easy.
        rewrite /= !andb_and in wf_x.
        apply eval_wellformed in e3_1; try easy.
        rewrite /= cstr_blocks !andb_and in e3_1.
        now eapply nth_error_forallb in e4.
      + exfalso. now destruct with_prop_case.
      + now exfalso.
    - eapply f_delta; try easy.
      eapply eval_cofix_ind; try easy.
      apply lookup_env_wellformed in isdecl; try easy.
      unfold wf_global_decl in isdecl.
      now rewrite e in isdecl.
    - now exfalso.
    - eapply f_proj_block; try easy.
      { now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x. }
      eapply eval_cofix_ind; try easy.
      rewrite /= !andb_and in wf_x.
      apply eval_wellformed in e2; try easy.
      rewrite /= cstr_blocks !andb_and in e2.
      now eapply nth_error_forallb in e5.
    - exfalso. now destruct with_prop_case.
    - now exfalso.
    - eapply f_construct_block; try easy.
      clear e e0 e1.
      assert (forallb (wellformed Σ 0) args).
      { now rewrite /= cstr_blocks !andb_and in wf_x. }
      clear wf_x.
      induction a; constructor.
      + eapply eval_cofix_ind; try easy.
        now rewrite /= andb_and in H. 
      + apply IHa. now rewrite /= andb_and in H. 
    - eapply f_app_cong; try easy.
      + now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x.
      + now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x.
    - eapply f_prim.
      depelim e; constructor.
      + subst a a'.
        assert (forallb (wellformed Σ 0) v).
        { now rewrite /= /test_prim /test_array_model /= !andb_and in wf_x. }
        clear wf_x.
        induction ev; constructor.
        * eapply eval_cofix_ind; try easy.
          now rewrite /= andb_and in H. 
        * apply IHev. now rewrite /= andb_and in H. 
      + now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x.
    - eapply f_force; try easy.
      { now eapply eval_cofix_ind; try rewrite /= !andb_and in wf_x. }
      eapply eval_cofix_ind; try easy.
      rewrite /= andb_and in wf_x.
      apply eval_wellformed in e1; try easy.
      now rewrite /= andb_and in e1.
    - now eapply f_atom.
  Qed.
End eval_cofix_ind.


Print Assumptions eval_cofix_ind.

(* (
  ∀ (ip : inductive × nat) (mfix : mfixpoint term) (idx : nat) (args : list term) (discr : term) (narg : nat) (fn : term) (brs : list
  (list
  name
  × term)) (res : term) (e : eval
  Σ
  discr
  (mkApps
  (tCoFix
  mfix
  idx)
  args)),
  P discr (mkApps (tCoFix mfix idx) args) e
  -> ∀ (e0 : cunfold_cofix mfix idx = Some (narg, fn)) (e1 : eval Σ (tCase ip (mkApps fn args) brs) res),
  P (tCase ip (mkApps fn args) brs) res e1 -> P (tCase ip discr brs) res (eval_cofix_case Σ ip mfix idx args discr narg fn brs
  res e e0 e1)
  )
  (
    ∀ (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term) (discr : term) (narg : nat) (fn res : term) (e : eval
    Σ
    discr
    (mkApps
    (tCoFix
    mfix
    idx)
    args)),
    P discr (mkApps (tCoFix mfix idx) args) e
    -> ∀ (e0 : cunfold_cofix mfix idx = Some (narg, fn)) (e1 : eval Σ (tProj p (mkApps fn args)) res),
    P (tProj p (mkApps fn args)) res e1 -> P (tProj p discr) res (eval_cofix_proj Σ p mfix idx args discr narg fn res e e0 e1)
  )
*)
