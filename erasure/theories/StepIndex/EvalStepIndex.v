(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv EWellformed EWcbvEval.
From MetaRocq.Utils Require Import bytestring MRString.
From MetaRocq.Erasure Require Import EWcbvEvalCstrsAsBlocksFixLambdaInd.
From MetaRocq.Erasure.StepIndex Require Import Tactics Utils SubstLemmas Values Primitives.
From Stdlib Require Import Relations.Relations.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.
Set Default Proof Using "Type*".

Section Wcbv.
  Context (Σ : global_declarations).
  
  Unset Elimination Schemes.
  (*
    - eval_box : OK
    - eval_beta : OK
    - eval_zeta : OK
    - eval_iota : OK
    - eval_iota_block : OK
    - eval_iota_sing : Can be skipped
    - eval_fix : our fix are unguarded
    - eval_fix_value : our fix are unguarded
    - eval_fix' : OK
    - eval_cofix_case : OK but unsatisfactory
    - eval_cofix_proj : OK but unsatisfactory
    - eval_delta : OK
    - eval_proj : OK
    - eval_proj_block : OK
    - eval_proj_prop : can be skipped
    - eval_construct : OK, might be removed, TODO: remove
    - eval_construct_block : OK 
    - eval_app_cong : OK by eval_cofix_app
    - eval_prim : OK 
    - eval_atom : OK I think *)

  Inductive eval (Γ : environment) : term -> value -> nat -> Type :=
  | eval_box :
      eval Γ tBox vBox 0

  | eval_box_app a t v n1 n2 :
      eval Γ a vBox n1 ->
      eval Γ t v n2 ->
      eval Γ (tApp a t) vBox ((n1 + 1) + (n2 + 1))

  (** Reductions *)
  | eval_var n v :
      nth_error Γ n = Some v ->
      eval Γ (tRel n) v 0

  (** Beta *)
  | eval_beta f na b a a' res Γ' c1 c2 c3 :
      eval Γ f (vClos na b Γ') c1 ->
      eval Γ a a' c2 ->
      eval (a' :: Γ') b res c3 ->
      eval Γ (tApp f a) res ((c1 + 1) + (c2 + 1) + (c3 + 1))

  | eval_lambda na b :
      eval Γ (tLambda na b) (vClos na b Γ) 0

  (** Let *)
  | eval_zeta na b0 b0' b1 res c1 c2 :
      eval Γ b0 b0' c1 ->
      eval (b0' :: Γ) b1 res c2 ->
      eval Γ (tLetIn na b0 b1) res ((c1 + 1) + (c2 + 1))

  (** Case *)
  | eval_iota_block ind cdecl discr c args brs br res c1 c2 : (* Changed pars to not be 0 *)
      eval Γ discr (vConstruct ind c args) c1 ->
      constructor_isprop_pars_decl Σ ind c = Some (false, 0, cdecl) ->
      nth_error brs c = Some br ->
      #|args| = cdecl.(cstr_nargs) ->
      #|args| = #|br.1| ->
      eval ((List.rev args) ++ Γ) br.2 res c2 ->
      eval Γ (tCase (ind, 0) discr brs) res ((c1 + 1) + (c2 + 1))

  | eval_proj p cdecl discr args a n :
      eval Γ discr (vConstruct (proj_ind p) 0 args) n ->
      constructor_isprop_pars_decl Σ (proj_ind p) 0 = Some (false, proj_npars p, cdecl) ->
      #|args| = proj_npars p + cstr_nargs cdecl ->
      nth_error args (proj_npars p + proj_arg p) = Some a ->
      eval Γ (tProj p discr) a (n + 1)


  (** Fix unfolding, without guard *)
  | eval_fix_unfold f mfix idx a av fn res Γ' c1 c2 c3 :
      eval Γ f (vRecClos mfix idx Γ') c1 ->
      cunfold_fix mfix idx = Some fn ->
      eval Γ a av c2 ->
      eval (av :: (fix_env mfix Γ') ++ Γ') fn res c3 ->
      eval Γ (tApp f a) res ((c1 + 1) + (c2 + 1) + (c3 + 1))

  | eval_fix mfix idx :
      eval Γ (tFix mfix idx) (vRecClos mfix idx Γ) 0


  | eval_cofix mfix idx :
      eval Γ (tCoFix mfix idx) (vCoFixClos mfix idx Γ []) 0

  | eval_cofix_app arg arg' a mfix idx env args n1 n2 :
      eval Γ a (vCoFixClos mfix idx env args) n1 ->
      eval Γ arg arg' n2 ->
      eval Γ (tApp a arg) (vCoFixClos mfix idx env (args ++ [arg'])) ((n1 + 1) + (n2 + 1))
  
  
      

  | eval_cofix_case discr mfix idx env args fn ip brs res n1 n2 :
      eval Γ discr (vCoFixClos mfix idx env args) n1 ->
      cunfold_cofix mfix idx = Some fn ->
      eval Γ (tCase ip (mkApps (substlg (map term_of_val (cofix_env mfix env ++ env)) 0 fn) (map term_of_val args)) brs) res n2 ->
      eval Γ (tCase ip discr brs) res ((n1 + 1) + (n2 + 1))
      (* 
      eval Γ discr (vCoFixClos mfix idx env args) n1 ->
      cunfold_cofix mfix idx = Some fn ->
      eval (cofix_env mfix env ++ env) (mkApps fn (map term_of_val args)) (vConstruct ind c con_args) n2 ->
      constructor_isprop_pars_decl Σ ind c = Some (false, 0, cdecl) ->
      nth_error brs c = Some br ->
      #|con_args| = cdecl.(cstr_nargs) ->
      #|con_args| = #|br.1| ->
      eval ((List.rev con_args) ++ Γ) br.2 res n3 ->
      eval Γ (tCase (ind, 0) discr brs) res (n1 + n2 + n3 + 1) *)

    (* 
      Problèmes:
      - Pas d'hypothèse de récurrence sur `mkApps fn (map term_of_val args')`
      - On est pas sûr que `mkApps fn (map term_of_val args')` se réduise en construct, ça pourrait être un cofix
        (techniquement évité par la contrainte de productivité je pense, mais l'info est probablement pas conservée à l'effacement)
      Solution envisageable:
      evaluer `tCase (mkApps (substl (cofix_env mfix env ++ env) fn) (map term_of_val args)) brs`, on perd un peu l'intérêt de l'environnement, mais on gagne le fait que ce qu'on veut prouver est prouvable

    *)

  | eval_cofix_proj discr mfix idx env args fn p res n1 n2 :
      eval Γ discr (vCoFixClos mfix idx env args) n1 ->
      cunfold_cofix mfix idx = Some fn ->
      eval Γ (tProj p (mkApps (substlg (map term_of_val (cofix_env mfix env ++ env)) 0 fn) (map term_of_val args))) res n2 ->
      eval Γ (tProj p discr) res ((n1 + 1) + (n2 + 1))
  (* 
  
  eval_cofix_proj
     : ∀ (Σ0 : global_context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list
  term) (discr : term) (narg : nat) (fn
  res : term),
  eval Σ0 discr (mkApps (tCoFix mfix idx) args)
  → EGlobalEnv.cunfold_cofix mfix idx = Some (narg, fn)
  → eval Σ0 (tProj p (mkApps fn args)) res
  → eval Σ0 (tProj p discr) res
*)

      (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) res cost :
      decl.(cst_body) = Some body ->
      eval [] body res cost ->
      eval Γ (tConst c) res (cost + 1)
      (* TODO see if +1 needed, I think so *)
    (* TODO: see interactions with Σ consisting of values *)

  (** Constructor congruence: we do not allow over-applications *)
  | eval_construct_block ind c mdecl idecl cdecl args args' cs  :
      lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
      #|args| = ind_npars mdecl + cstr_nargs cdecl -> (* see if we add `ind_npars mdecl` or ask for no params *)
      All3 (eval Γ) args args' cs ->
      eval Γ (tConstruct ind c args) (vConstruct ind c args') (list_sum cs + #|cs|)

  | eval_prim p p' c :
      eval_primitive_step_index (eval Γ) p p' c ->
      eval Γ (tPrim p) (vPrim p') c

  | eval_lazy t : eval Γ (tLazy t) (vLazy t Γ) 0

  | eval_force Γ' t t' v c1 c2 :
      eval Γ t (vLazy t' Γ') c1 ->
      eval Γ' t' v c2 ->
      eval Γ (tForce t) v (c1 + c2 + 1)
  .

  Section EvalInd.
    Variable (P : ∀ (Γ : environment) (t : term) (v : value) (cost : nat), eval Γ t v cost -> Type).
    Variable f_box : ∀ {Γ}, P Γ tBox vBox 0 (eval_box Γ).
    Variable f_box_app : ∀ {Γ a t v n1 n2 e1 e2},
      P Γ a vBox n1 e1 ->
      P Γ t v n2 e2 ->
      P Γ (tApp a t) vBox _ (eval_box_app Γ a t v n1 n2 e1 e2).
    Variable f_var : 
      ∀ {Γ n v e},
      P Γ (tRel n) v 0 (eval_var Γ n v e).
    Variable f_beta : 
      ∀ {Γ f1 na b a a' res Γ' c1 c2 c3 e e0 e1},
      P Γ f1 (vClos na b Γ') c1 e ->
      P Γ a a' c2 e0 ->
      P (a' :: Γ') b res c3 e1 ->
      P Γ (tApp f1 a) res _ (eval_beta Γ f1 na b a a' res Γ' c1 c2 c3 e e0 e1).
    Variable f_lambda :
      ∀ {Γ na b},
      P Γ (tLambda na b) (vClos na b Γ) 0 (eval_lambda Γ na b).
    Variable f_zeta : 
      ∀ {Γ na b0 b0' b1 res c1 c2 e e0},
      P Γ b0 b0' c1 e ->
      P (b0' :: Γ) b1 res c2 e0 ->
      P Γ (tLetIn na b0 b1) res _ (eval_zeta Γ na b0 b0' b1 res c1 c2 e e0).
    Variable f_iota_block : 
      ∀ {Γ ind cdecl discr c args brs br res c1 c2 e e0 e1 e2 e3 e4},
        P Γ discr (vConstruct ind c args) c1 e ->
        P (List.rev args ++ Γ) br.2 res c2 e4 ->
        P Γ (tCase (ind, 0) discr brs) res _ (eval_iota_block Γ ind cdecl discr c args brs br res c1 c2 e e0 e1 e2 e3 e4).
    Variable f_proj : ∀ {Γ p cdecl discr args a n e1 e2 e3 e4},
      P Γ discr (vConstruct (proj_ind p) 0 args) n e1 ->
      P Γ (tProj p discr) a (n + 1) (eval_proj Γ p cdecl discr args a n e1 e2 e3 e4).
    Variable f_fix_unfold :
      ∀ {Γ f mfix idx a av fn res Γ' c1 c2 c3 e e0 e1 e2},
      P Γ f (vRecClos mfix idx Γ') c1 e ->
      P Γ a av c2 e1 ->
      P (av :: (fix_env mfix Γ') ++ Γ') fn res c3 e2 ->
      P Γ (tApp f a) res _ (eval_fix_unfold Γ f mfix idx a av fn res Γ' c1 c2 c3 e e0 e1 e2).
    Variable f_fix : 
      ∀ {Γ mfix idx},
      P Γ (tFix mfix idx) (vRecClos mfix idx Γ) 0 (eval_fix Γ mfix idx).
    Variable f_cofix :
      ∀ {Γ mfix idx},
      P _ _ _ _ (eval_cofix Γ mfix idx).
    Variable f_cofix_app : 
      ∀ {Γ arg arg' a mfix idx env args n1 n2}
        { e1 : eval Γ a (vCoFixClos mfix idx env args) n1 }
        { e2 : eval Γ arg arg' n2 },
        P _ _ _ _ e1 ->
        P _ _ _ _ e2 ->
        P Γ _ _ _ (eval_cofix_app Γ arg arg' a mfix idx env args n1 n2 e1 e2). 
    Variable f_cofix_case : 
      ∀ {Γ discr mfix idx env args fn ip brs res n1 n2}
        { e1 : eval Γ discr (vCoFixClos mfix idx env args) n1}
        { heq1 : cunfold_cofix mfix idx = Some fn }
        { e2 : eval Γ 
          (tCase ip (mkApps (substlg (map term_of_val (cofix_env mfix env ++ env)) 0 fn) (map term_of_val args)) brs) 
          res n2 },
        P _ _ _ _ e1 ->
        P _ _ _ _ e2 ->
        P Γ _ _ _
          (eval_cofix_case 
            Γ discr mfix idx env args fn ip brs res n1 n2 e1 heq1 e2). 
      Variable f_cofix_proj : 
      ∀ {Γ discr mfix idx env args fn p res n1 n2}
        { e1 : eval Γ discr (vCoFixClos mfix idx env args) n1}
        { heq1 : cunfold_cofix mfix idx = Some fn }
        { e2 : eval Γ 
          (tProj p (mkApps (substlg (map term_of_val (cofix_env mfix env ++ env)) 0 fn) (map term_of_val args))) 
          res n2 },
        P _ _ _ _ e1 ->
        P _ _ _ _ e2 ->
        P Γ _ _ _
          (eval_cofix_proj 
            Γ discr mfix idx env args fn p res n1 n2 e1 heq1 e2). 
    Variable f_delta :
      ∀ {Γ c decl body res isdecl cost e e0},
      P [] body res cost e0 ->
      P Γ (tConst c) res _ (eval_delta Γ c decl body isdecl res cost e e0).
    Variable f_constr_block : 
        ∀ {Γ ind c mdecl idecl cdecl args args' cs}
          (e : lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl)) 
          (l : #|args| = ind_npars mdecl + cstr_nargs cdecl) 
          (a : All3 (eval Γ) args args' cs) (IHa : All3_over a (P Γ)), 
        P Γ (tConstruct ind c args) (vConstruct ind c args') _
          (eval_construct_block Γ ind c mdecl idecl cdecl args args' cs  e l a).
    Variable f_prim : 
      ∀ {Γ p p' c} 
        (ev : eval_primitive_step_index (eval Γ) p p' c)
        (evih : eval_primitive_step_index_ind (eval Γ) (P Γ) _ _ _ ev),
      P Γ (tPrim p) (vPrim p') _ (eval_prim _ _ _ _ ev).
    Variable f_lazy :
      ∀ {Γ t}, 
      P Γ (tLazy t) (vLazy t Γ) 0 (eval_lazy _ _).
    Variable f_force : 
      ∀ {Γ Γ' t t' v c1 c2} 
        {ev0 : eval Γ t (vLazy t' Γ') c1} 
        {ev1 : eval Γ' t' v c2},
      P _ _ _ c1 ev0 -> 
      P _ _ _ c2 ev1 ->
      P _ _ _ (c1 + c2 + 1) (eval_force _ _ _ _ _ c1 c2 ev0 ev1).

    Fixpoint eval_rect {Γ t v c} t_eval_v
      : P Γ t v c t_eval_v :=
        match t_eval_v as e0 in (eval _ t0 v0 c0) return (P Γ t0 v0 c0 e0) with
        | @eval_box _ => f_box
        | @eval_box_app _ a t v n1 n2 e1 e2 => f_box_app (eval_rect e1) (eval_rect e2)
        | @eval_var _ na v0 e0 => f_var
        | @eval_beta _ f10 na b a a' res Γ' c1 c2 c3 e0 e1 e2 => f_beta (eval_rect e0) (eval_rect e1) (eval_rect e2)
        | @eval_lambda _ na b => f_lambda
        | @eval_zeta _ na b0 b0' b1 res c1 c2 e0 e1 => f_zeta (eval_rect e0) (eval_rect e1)
        | @eval_iota_block _ ind cdecl discr c args brs br res c1 c2 e0 e1 e2 e3 e4 e5 => f_iota_block (eval_rect e0) (eval_rect e5)
        | @eval_proj _ _ _ _ _ _ _ e _ _ _  => f_proj (eval_rect e)
        | @eval_fix_unfold _ f10 mfix idx a av fn res Γ' c1 c2 c3 e0 e1 e2 e3 =>
            f_fix_unfold (eval_rect e0) (eval_rect e2) (eval_rect e3)
        | @eval_fix _ mfix idx => f_fix
        | @eval_cofix _ mfix idx => f_cofix
        | @eval_cofix_app _ arg arg' a mfix idx env args n1 n2 e1 e2 => 
            f_cofix_app (eval_rect e1) (eval_rect e2)
        | @eval_cofix_case _ discr mfix idx env args fn ip brs res n1 n2 e1 heq1 e2 => 
              f_cofix_case (eval_rect e1) (eval_rect e2)
        | @eval_cofix_proj _ discr mfix idx env args fn p res n1 n2 e1 heq1 e2 => 
              f_cofix_proj (eval_rect e1) (eval_rect e2)
        | @eval_delta _ c decl body isdecl res cost e0 e1 => f_delta (eval_rect e1)
        | @eval_construct_block _ ind c mdecl idecl cdecl args args' cs e0 l a =>
            f_constr_block e0 l a (map_All3_dep _ (@eval_rect Γ) a)
        | @eval_prim _ p p' c ev => f_prim ev (map_eval_primitive_step_index (@eval_rect Γ) ev)
        | @eval_lazy _ t => f_lazy
        | @eval_force _ Γ' t t' v c1 c2 ev ev' => f_force (eval_rect ev) (eval_rect ev')
        end.
  End EvalInd.
  Definition eval_rec (P : ∀ Γ t v cost, eval Γ t v cost -> Set) := @eval_rect P.
  Definition eval_ind (P : ∀ Γ t v cost, eval Γ t v cost -> Prop) := @eval_rect P.
  Set Elimination Schemes.

End Wcbv.



Lemma eval_SI_wellformed_val {efl : EEnvFlags} Σ Γ e v n :
  cstr_as_blocks ->
  has_tApp ->
  wf_glob Σ ->
  forallb (wellformed_val Σ) Γ ->
  wellformed Σ #|Γ| e ->
  eval Σ Γ e v n ->
  wellformed_val Σ v.
Proof.
  intros cstr_blocks htApp wf_Σ wf_Γ wf_e h_eval.
  induction h_eval; simple.
  - easy.
  - now eapply wf_Γ, nth_error_In.
  - apply IHh_eval3; try easy; now intros ? [-> | hIn].
  - easy.
  - apply IHh_eval2; try easy; now intros ? [-> | hIn].
  - destruct IHh_eval1; try easy. 
    apply IHh_eval2.
    + now intros x [?%in_rev|?]%in_app_or.
    + rewrite e3.
      apply wf_e.
      now eapply nth_error_In.
  - apply IHh_eval; try easy.
    now eapply nth_error_In.
  - unfold wf_fix, test_def in *; simple.
    destruct IHh_eval1 as [[[? ?] ?] [? ?]]; try easy.
    apply IHh_eval3; last first.
    { unfold cunfold_fix in e0.
      destruct (nth_error mfix idx) as [[? [] ?]|] eqn:heq ; simple; try easy.
      injection e0 as e0; subst.
      unshelve epose proof H3 _ _; first shelve.
      { eapply nth_error_In, heq. }
      simple. easy. }
    intros ? [-> | [hIn | hIn]%in_app_iff]; try easy.
    rewrite fix_env_map in_map_iff in hIn.
    destruct hIn as (? & ? & hIn%in_rev%in_seq); subst.
    simple. unfold wf_fix, test_def; simple.
    repeat split; try easy.
    now apply Nat.ltb_lt.
  - easy.
  - easy.
  - unshelve epose proof IHh_eval1 _ _; try easy.
    unshelve epose proof IHh_eval2 _ _; try easy.
    repeat split; try easy.
    now intros x [hIn | [-> | []]]%in_app_iff.
  - unshelve epose proof IHh_eval1 _ _ as h; try easy.
    unfold wf_fix in h; simple.
    destruct h as [[[? wf_env] wf_args] [idx_lt_mfix%Nat.ltb_lt wf_mfix]].
    unfold test_def in wf_mfix.
    unshelve epose proof IHh_eval2 _ _ as h; try easy.
    repeat split; try easy.
    rewrite wellformed_mkApps; simple; split.
    + apply wellformed_substl; simple.
      * rewrite cofix_env_map map_map_compose.
        intros x [(? & ? & hIn%in_rev%in_seq)%in_map_iff | (? & ? & hIn)%in_map_iff]%in_app_iff; subst; simple; last now apply wellformed_val_wellformed.
        unfold wf_fix; simple. repeat split; try easy.
        { now apply Nat.ltb_lt. }
        intros.
        apply wellformed_substlg; simple; last easy.
        intros ? (? & ? & ?)%in_map_iff ?; subst; simple.
        now apply wellformed_val_wellformed.
      * assert (wellformed Σ (#|mfix| + #|env|) fn); last now eapply wellformed_up.
        unfold cunfold_cofix in heq1.
        destruct (nth_error mfix idx) as [r |] eqn:heq; last easy.
        simple. injection heq1 as ?; subst.
        now apply nth_error_In in heq.
    + now intros ? ?; apply wellformed_val_wellformed.
  - unshelve epose proof IHh_eval1 _ _ as h; try easy.
    unfold wf_fix in h; simple.
    destruct h as [[[? wf_env] wf_args] [idx_lt_mfix%Nat.ltb_lt wf_mfix]].
    unfold test_def in wf_mfix.
    unshelve epose proof IHh_eval2 _ _ as h; try easy.
    repeat split; try easy.
    rewrite wellformed_mkApps; simple; split.
    + apply wellformed_substl; simple.
      * rewrite cofix_env_map map_map_compose.
        intros x [(? & ? & hIn%in_rev%in_seq)%in_map_iff | (? & ? & hIn)%in_map_iff]%in_app_iff; subst; simple; last now apply wellformed_val_wellformed.
        unfold wf_fix; simple. repeat split; try easy.
        { now apply Nat.ltb_lt. }
        intros.
        apply wellformed_substlg; simple; last easy.
        intros ? (? & ? & ?)%in_map_iff ?; subst; simple.
        now apply wellformed_val_wellformed.
      * assert (wellformed Σ (#|mfix| + #|env|) fn); last now eapply wellformed_up.
        unfold cunfold_cofix in heq1.
        destruct (nth_error mfix idx) as [r |] eqn:heq; last easy.
        simple. injection heq1 as ?; subst.
        now apply nth_error_In in heq.
    + now intros ? ?; apply wellformed_val_wellformed.
  - apply IHh_eval; first easy.
    pose proof lookup_env_wellformed wf_Σ isdecl.
    simple.
  - rewrite /lookup_constructor_pars_args e;
    rewrite cstr_blocks /lookup_constructor_pars_args e in wf_e; simple.
    assert (ind_npars mdecl + cstr_nargs cdecl = #|args|) as heq by now apply eqb_eq.
    assert (#|args'| = #|args|) as heq'.
    { revert a IHa; clear; intros a _. induction a in |- *; now simple. }
    simple. repeat split; try easy.
    destruct wf_e as [_ [_ wf_e]].
    revert a IHa wf_e wf_Γ; clear.
    intros a IH hwf wf_Γ.
    induction a; simple; try easy.
    destruct IH as [? ?]; simple.
    intros v [[] | hIn]; simple; try easy.
    + apply i; simple. now apply hwf.
    + apply IHa; now simple.
  - inversion evih; subst; unfold test_prim, test_array_model in *; simple; repeat split; try easy.
    destruct wf_e as [? wf_e].
    revert wf_e wf_Γ X. clear.
    induction ev0; simple; try easy.
    intros ? wf_Γ [? ?]; simple.
    intros ? [<- | ?]; try easy.
    + now apply i.
    + now apply IHev0.
  - easy.
  - easy.
Qed.


Equations extract {efl : EEnvFlags} {Σ args} {P : value -> nat -> value -> Type} 
  (a1 : All (λ v, wellformed_val Σ v → ∑ n v', P v n v') args) 
  (a2 : All (λ v, wellformed_val Σ v) args) :
  list nat × list value :=
    extract All_nil All_nil := ([], []);
    extract (All_cons h t) (All_cons wf_h wf_t) with h wf_h, extract t wf_t := {
      | (n; v; a), (ln, lv) => (n :: ln, v :: lv)
    }.


Definition extract_ns {efl : EEnvFlags} {Σ args} {P : value -> nat -> value -> Type} 
  (a1 : All (λ v, wellformed_val Σ v → ∑ n v', P v n v') args)
  (a2 : All (λ v, wellformed_val Σ v) args) := fst (extract a1 a2).


Definition extract_vs {efl : EEnvFlags} {Σ args} {P : value -> nat -> value -> Type} 
  (a1 : All (λ v, wellformed_val Σ v → ∑ n v', P v n v') args) 
  (a2 : All (λ v, wellformed_val Σ v) args) := snd (extract a1 a2).


Lemma All3_app_inv_first {A B C} (P : A -> B -> C -> Type) l1_1 l1_2 l2 l3 :
  All3 P (l1_1 ++ l1_2) l2 l3 ->
  ∑ l2_1 l2_2 l3_1 l3_2,
    l2 = l2_1 ++ l2_2 × 
    l3 = l3_1 ++ l3_2 ×
    All3 P l1_1 l2_1 l3_1 ×
    All3 P l1_2 l2_2 l3_2.
Proof.
  intros hAll.
  induction l1_1 as [|h1 l1_1 IH] in l2, l3, hAll |- *.
  - simple. exists [], l2, [], l3.
    now repeat split.
  - simple.
    inversion hAll as [|? h2 h3 ? l2' l3' Phs hAll']; subst.
    destruct (IH _ _ hAll') as (l2_1 & l2_2 & l3_1 & l3_2 & heq1 & heq2 & hAll1 & hAll2); subst.
    exists (h2 :: l2_1), l2_2, (h3 :: l3_1), l3_2.
    now repeat split.
Qed.


Lemma All3_snoc_inv_first {A B C} (P : A -> B -> C -> Type) l1 e1 l2 l3 :
  All3 P (l1 ++ [e1]) l2 l3 ->
  ∑ l2' e2 l3' e3,
    l2 = l2' ++ [e2] × 
    l3 = l3' ++ [e3] ×
    All3 P l1 l2' l3' ×
    P e1 e2 e3.
Proof.
  intros hAll.
  apply All3_app_inv_first in hAll as (? & ? & ? & ? & ? & ? & ? & hAll'); subst.
  inversion hAll'; subst.
  inversion X0; subst.
  now repeat eexists.
Qed.


Lemma eval_cofix_mkApps Σ Γ a mfix idx env n args args' ns :
  eval Σ Γ a (vCoFixClos mfix idx env []) n ->
  All3 (eval Σ Γ) args args' ns ->
  eval Σ Γ (mkApps a args) (vCoFixClos mfix idx env args') ((n + list_sum ns + 2 * #|ns|)).
Proof.
  intros eval_a eval_args.
  induction args
  as [|arg args IH]
  using list_rect_rev
  in args', ns, eval_args |- *.
  { simple. inversion eval_args; simple. }
  apply All3_snoc_inv_first in eval_args 
    as (args'' & arg' & ns' & n' & ? & ? & hAll' & eval_arg); subst.
  rewrite list_sum_app.
  simple.
  epose proof eval_cofix_app _ _ _ _ _ _ _ _ _ _ _ (IH _ _ hAll') eval_arg.
  rewrite mkApps_app /=.
  simple.
  now match goal with 
  | h: eval _ _ _ _ ?n1 
    |- eval _ _ _ _ ?n2 => replace n2 with n1
  end.
Qed.



Lemma eval_SI_val {efl : EEnvFlags} Σ Γ v :
  has_tApp ->
  cstr_as_blocks ->
  wellformed_val Σ v ->
  ∑ (n : nat) v', term_of_val v = term_of_val v' × eval Σ Γ (term_of_val v) v' n.
Proof.
  intros hApp cstr_blocks h_wf.
  induction v.
  - repeat econstructor.
  - simple.
    unfold lookup_constructor_pars_args in h_wf.
    destruct (lookup_constructor Σ ind c) as [[[mdecl idecl] cdecl] |] eqn:heq; simpl in *; last easy.
    assert (All (wellformed_val Σ) args) as X' by now simple.
    pose args' := @extract_vs efl _ _ _ X X'.
    assert (map term_of_val args = map term_of_val args').
    { clear. subst args'; unfold extract_vs. 
      funelim (extract X X'); simple; try easy.
      destruct a as [? ?]. rewrite Heq in Hind.
      now f_equal. }
    eexists. exists (vConstruct ind c args'); simple; split; try (f_equal; easy).
    eapply eval_construct_block with (cs := extract_ns X X'); simple; try easy.
    { now assert (#|args| = ind_npars mdecl + cstr_nargs cdecl) as h by now apply eqb_eq. }
    unfold args', extract_vs, extract_ns.
    clear. funelim (extract X X'); simple; constructor; try easy.
    { now destruct a. }
    now rewrite Heq in Hind.
  - exists 0, (vClos na (substlg (map term_of_val env) 1 b) Γ); split; simple; try constructor.
    f_equal.
    unshelve epose proof closed_substlg 1 b (map term_of_val env) _ _ as h.
    { simple; intros ? (x & <- & hIn)%in_map_iff n.
      now eapply wellformed_closed, wellformed_val_wellformed. }
    { simple. now eapply wellformed_closed. }
    revert h. clear.
    induction Γ; simple; first reflexivity; intros h.
    rewrite csubst_closed; now simple.
  - exists 0, 
    (vRecClos (map (map_def (substlg (map term_of_val env) #|b|)) b) idx Γ);
      split; simple; last constructor.
    f_equal.
    rewrite map_map_compose. apply All_map_eq; simple.
    intros x hIn; simple. 
    unfold map_def; simple.
    f_equal.
    unshelve epose proof closed_substlg #|b| (dbody x) (map term_of_val env) _ _ as h.
    { simple; intros ? (? & <- & ?)%in_map_iff n.
      now eapply wellformed_closed, wellformed_val_wellformed. }
    { unfold wf_fix, test_def in h_wf; simple.
      simple. now eapply wellformed_closed. }
    revert h. clear.
    induction Γ; simple; first reflexivity; intros h.
    rewrite csubst_closed; now simple.
  - assert (All (wellformed_val Σ) args) as X' by now simple.
    pose args' := extract_vs X0 X'.
    assert (map term_of_val args = map term_of_val args').
    { clear. subst args'; unfold extract_vs. 
      funelim (extract X0 X'); simple; try easy.
      destruct a as [? ?]. rewrite Heq in Hind.
      now f_equal. }
    exists (list_sum (extract_ns X0 X') + 2 * #|extract_ns X0 X'|).
    eexists (vCoFixClos (map (map_def (substlg (map term_of_val env) #|b|)) b) idx Γ args'); simpl in *; split; last first.
    + rewrite -(Nat.add_0_l (list_sum _)). eapply eval_cofix_mkApps.
      { simple. constructor. }
      unfold args', extract_vs, extract_ns.
      clear. funelim (extract X0 X'); simple; constructor; try easy.
      * apply a. 
      * now rewrite Heq in Hind.
    + simple. f_equal; last easy. f_equal.
      rewrite map_map_compose.
      apply All_map_eq.
      simple.
      intros [] hIn.
      unfold map_def; simple.
      f_equal.
      erewrite (substlg_closed (substlg _ _ _)); try easy.
      unfold wf_fix, test_def in h_wf; simple.
      apply h_wf in hIn; simple.
      apply closed_substlg; simple; try easy.
      * intros ? (x & ? & hIn')%in_map_iff k; subst.
        now eapply wellformed_closed, wellformed_val_wellformed.
      * now eapply wellformed_closed.
  - simple; inversion X as [| | | ? [? ?]]; subst; unfold map_prim; simple;
    try lazymatch goal with
    | |- context[tPrim (?t; ?c _ ?m) = _] =>
        exists 0, (vPrim (t; @c value m)); split; repeat constructor
    end.
    destruct a as [default values]; unfold map_array_model, test_prim, test_array_model in *; simple.
    assert (All (wellformed_val Σ) values) as X' by now simple.
    pose values' := @extract_vs efl _ _ _ a0 X'.
    assert (map term_of_val values = map term_of_val values').
    { clear. subst values'; unfold extract_vs. 
      funelim (extract a0 X'); simple; try easy.
      destruct a as [? ?]. rewrite Heq in Hind.
      now f_equal. }
    destruct s as (n_default & v'_default & eq_default & eval_default); first easy.
    pose new_a := {| array_default := v'_default; array_value := values' |}.
    eexists. exists (vPrim (Primitive.primArray; primArrayModel new_a)).
    split; simple.
    { unfold map_prim, map_array_model; simple. easy. }
    constructor. eapply evalPrimStepIndexArray with (ns := extract_ns a0 X'); last easy.
    unfold new_a, values', extract_ns, extract_vs in *.
    clear. funelim (extract a0 X'); simple; constructor; try easy.
    { now destruct a. }
    now rewrite Heq in Hind.
  - exists 0, (vLazy (substlg (map term_of_val env) 0 p) Γ); split; last now constructor.
    simple; f_equal.
    unshelve epose proof closed_substlg 0 p (map term_of_val env) _ _ as h.
    { simple; intros ? (? & <- & ?)%in_map_iff n.
      now eapply wellformed_closed, wellformed_val_wellformed. }
    { simple. now eapply wellformed_closed. }
    revert h. clear.
    induction Γ; simple; first reflexivity; intros h.
    rewrite csubst_closed; now simple.
Qed.


Lemma isConstructApp_isvConstr 
  {efl : EEnvFlags} {wfl : WcbvFlags} Σ Γ t v n :
  isConstructApp t ->
  eval Σ Γ t v n ->
  isvConstr v.
Proof.
  unfold isConstructApp.
  intros hConstrApp heval.
  induction heval; subst;
  rewrite ->?head_tApp in *; simple; try easy.
Qed.


Lemma isCoFixApp_isvCoFix 
  {efl : EEnvFlags} {wfl : WcbvFlags} Σ Γ t v n :
  isCoFix (head t) ->
  eval Σ Γ t v n ->
  isvCoFixClos v.
Proof.
  unfold isConstructApp.
  intros hConstrApp heval.
  induction heval; subst;
  rewrite ->?head_tApp in *; simple; try easy.
Qed.


Ltac find_contra := 
    let aux f lem a b h :=
      let h' := fresh in 
      assert (f (head (tApp a b))) as h'
      by (now rewrite h head_mkApps);
      rewrite head_tApp in h';
      now eapply lem in h'; 
        last eassumption
    in
    match goal with 
    | h : tApp ?a ?b = mkApps (tConstruct _ _ _) _ |- _ => aux isConstruct isConstructApp_isvConstr a b h
    | h : mkApps (tConstruct _ _ _) _ = tApp ?a ?b |- _ => aux isConstruct isConstructApp_isvConstr a b (eq_sym h)
    | h : tApp ?a ?b = mkApps (tCoFix _ _) _ |- _ => aux isCoFix isCoFixApp_isvCoFix a b h
    | h : mkApps (tCoFix _ _) _ = tApp ?a ?b |- _ => aux isCoFix isCoFixApp_isvCoFix a b (eq_sym h)
    end.

Ltac injections :=
  repeat (
    subst || simple ||
    match goal with
    | H: ?f _ = ?f _ |- _ => progress injection H as ?
    | H: ?f _ _ = ?f _ _ |- _ => progress injection H as ?
    | H: ?f _ _ _ = ?f _ _ _ |- _ => progress injection H as ?
    | H: ?f _ _ _ _ = ?f _ _ _ _ |- _ => progress injection H as ?
    | H: ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ => progress injection H as ?
    | H: ?f _ _ _ _ _ _ = ?f _ _ _ _ _ _ |- _ => progress injection H as ?
    end
  ).


Lemma eval_SI_deterministic
  {efl : EEnvFlags} {wfl : WcbvFlags} Σ Γ t v1 v2 n1 n2 :
  eval Σ Γ t v1 n1 ->
  eval Σ Γ t v2 n2 ->
  v1 = v2 ∧ n1 = n2.
Proof.
  intros eval1 eval2.
  induction eval1 in eval2, v2, n2 |- *; try solve[
    inversion eval2; subst; unfold declared_constant in *; solve[
      find_contra | my_discr | easy |
      injections;
      edestruct IHeval1; first eassumption;
      injections; 
      easy |
      injections;
      edestruct IHeval1_1; first eassumption;
      injections;
      edestruct IHeval1_2; first eassumption;
      injections;
      easy |
      injections;
      edestruct IHeval1_1; first eassumption;
      injections;
      edestruct IHeval1_2; first eassumption;
      injections;
      edestruct IHeval1_3; first eassumption;
      injections;
      easy
    ] 
  ].
  - inversion eval2; subst; try my_discr.
    assert (args' = args'0 ∧ cs = cs0); last easy.
    revert IHa X.
    clear.
    induction args in a, args', args'0, cs, cs0 |- *.
    { intros. inversion a. inversion X. easy. }
    intros.
    destruct args'; first inversion a.
    destruct args'0; first inversion X.
    remember (a0 :: args).
    remember (v :: args').
    destruct a eqn:heq; first discriminate; subst.
    injection Heql as ? ?.
    injection Heql0 as ? ?.
    subst.
    inversion X; subst.
    destruct IHa.
    edestruct IHargs; try easy.
    edestruct a; easy.
  - inversion eval2; subst; try my_discr.
    inversion evih; subst; try now inversion X.
    inversion X; subst.
    subst a a' a1 a2 a'0.
    assert (def' = def'0 ∧ n = n0) as (? & ?)
    by now edestruct H3.
    subst.
    assert (v' = v'0 ∧ ns = ns0); last easy.
    revert X0 X1.
    clear.
    induction v in ev0, v', v'0, ns, ns0 |- *.
    { intros. inversion ev0. inversion X1. easy. }
    intros.
    destruct v'; first inversion ev0.
    destruct v'0; first inversion X1.
    remember (a :: v).
    remember (v0 :: v').
    destruct ev0 eqn:heq; first discriminate; subst.
    injection Heql as ? ?.
    injection Heql0 as ? ?.
    subst.
    inversion X1; subst.
    destruct X0.
    edestruct IHv; try easy.
    edestruct a1; easy.
Qed.