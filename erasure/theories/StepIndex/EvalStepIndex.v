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
  Context {wfl : WcbvFlags}.
  Context (Σ : global_declarations).

  Unset Elimination Schemes.

  Inductive eval (Γ : environment) : term -> value -> nat -> Type :=
  | eval_box :
      eval Γ tBox vBox 0

  | eval_box_app a t v n1 n2 :
      eval Γ a vBox n1 ->
      eval Γ t v n2 ->
      eval Γ (tApp a t) vBox (n1 + n2 + 1)

  (** Reductions *)
  | eval_var n v :
      nth_error Γ n = Some v ->
      eval Γ (tRel n) v 0

  (** Beta *)
  | eval_beta f na b a a' res Γ' c1 c2 c3 :
      eval Γ f (vClos na b Γ') c1 ->
      eval Γ a a' c2 ->
      eval (a' :: Γ') b res c3 ->
      eval Γ (tApp f a) res (c1 + c2 + c3 + 1)

  | eval_lambda na b :
      eval Γ (tLambda na b) (vClos na b Γ) 0

  (** Let *)
  | eval_zeta na b0 b0' b1 res c1 c2 :
      eval Γ b0 b0' c1 ->
      eval (b0' :: Γ) b1 res c2 ->
      eval Γ (tLetIn na b0 b1) res (c1 + c2 + 1)

  (** Case *)
  | eval_iota_block ind cdecl discr c args brs br res c1 c2 :
      eval Γ discr (vConstruct ind c args) c1 ->
      constructor_isprop_pars_decl Σ ind c = Some (false, 0, cdecl) ->
      nth_error brs c = Some br ->
      #|args| = cdecl.(cstr_nargs) ->
      #|args| = #|br.1| ->
      eval ((List.rev args) ++ Γ) br.2 res c2 ->
      eval Γ (tCase (ind, 0) discr brs) res (c1 + c2 + 1)

  | eval_proj p cdecl discr args a n :
      with_constructor_as_block ->
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
      eval Γ (tApp f a) res (c1 + c2 + c3 + 1)

  | eval_fix mfix idx :
      eval Γ (tFix mfix idx) (vRecClos mfix idx Γ) 0

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) res cost :
      decl.(cst_body) = Some body ->
      eval [] body res cost ->
      eval Γ (tConst c) res (cost + 1) (* TODO see if +1 needed, I think so *)
  
  (** Constructor congruence: we do not allow over-applications *)
  | eval_construct_App ind c mdecl idecl cdecl args args' cs :
      ~~with_constructor_as_block ->
      lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
      #|args| <= ind_npars mdecl + cstr_nargs cdecl ->
      All3 (eval Γ) args args' cs ->
      eval Γ (mkApps (tConstruct ind c []) args) (vConstruct ind c args') (list_sum cs + 1)


  | eval_construct_block ind c mdecl idecl cdecl args args' cs  :
      with_constructor_as_block ->
      lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
      #|args| <= ind_npars mdecl + cstr_nargs cdecl -> (* see if we add `ind_npars mdecl` or ask for no params *)
      All3 (eval Γ) args args' cs ->
      eval Γ (tConstruct ind c args) (vConstruct ind c args') (list_sum cs + 1)

  (* | eval_construct_block_empty ind c mdecl idecl cdecl :
     lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
     eval Γ (tConstruct ind c []) (vConstruct ind c []) *)
  (* Seems handled by the case above *)

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
    Variable (P : ∀ {wfl : WcbvFlags} (Γ : environment) (t : term) (v : value) (cost : nat), eval Γ t v cost -> Type).
    Variable f_box : ∀ {Γ}, P Γ tBox vBox 0 (eval_box Γ).
    Variable f_box_app : ∀ {Γ a t v n1 n2 e1 e2},
      P Γ a vBox n1 e1 ->
      P Γ t v n2 e2 ->
      P Γ (tApp a t) vBox (n1 + n2 + 1) (eval_box_app Γ a t v n1 n2 e1 e2).
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
    Variable f_proj : ∀ {Γ p cdecl discr args a n cstr_blcks e1 e2 e3 e4},
      P Γ discr (vConstruct (proj_ind p) 0 args) n e1 ->
      P Γ (tProj p discr) a (n + 1) (eval_proj Γ p cdecl discr args a n cstr_blcks e1 e2 e3 e4).
    Variable f_fix_unfold :
      ∀ {Γ f mfix idx a av fn res Γ' c1 c2 c3 e e0 e1 e2},
      P Γ f (vRecClos mfix idx Γ') c1 e ->
      P Γ a av c2 e1 ->
      P (av :: (fix_env mfix Γ') ++ Γ') fn res c3 e2 ->
      P Γ (tApp f a) res _ (eval_fix_unfold Γ f mfix idx a av fn res Γ' c1 c2 c3 e e0 e1 e2).
    Variable f_fix : 
      ∀ {Γ mfix idx},
      P Γ (tFix mfix idx) (vRecClos mfix idx Γ) 0 (eval_fix Γ mfix idx).
    Variable f_delta :
      ∀ {Γ c decl body res isdecl cost e e0},
      P [] body res cost e0 ->
      P Γ (tConst c) res _ (eval_delta Γ c decl body isdecl res cost e e0).
    Variable f_constr_app :
        ∀ {Γ ind c mdecl idecl cdecl args args' cs}
          (c_as_bks : ~~with_constructor_as_block)
          (e : lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl)) 
          (l : #|args| ≤ ind_npars mdecl + cstr_nargs cdecl) 
          (a : All3 (eval Γ) args args' cs) (IHa : All3_over a (P Γ)), 
        P Γ (mkApps (tConstruct ind c []) args) (vConstruct ind c args') _
          (eval_construct_App Γ ind c mdecl idecl cdecl args args'  cs c_as_bks  e l a).
    Variable f_constr_block : 
        ∀ {Γ ind c mdecl idecl cdecl args args' cs}
          (c_as_bks : with_constructor_as_block)
          (e : lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl)) 
          (l : #|args| ≤ ind_npars mdecl + cstr_nargs cdecl) 
          (a : All3 (eval Γ) args args' cs) (IHa : All3_over a (P Γ)), 
        P Γ (tConstruct ind c args) (vConstruct ind c args') _
          (eval_construct_block Γ ind c mdecl idecl cdecl args args'  cs c_as_bks  e l a).
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
        | @eval_proj _ _ _ _ _ _ _ _ e _ _ _  => f_proj (eval_rect e)
        | @eval_fix_unfold _ f10 mfix idx a av fn res Γ' c1 c2 c3 e0 e1 e2 e3 =>
            f_fix_unfold (eval_rect e0) (eval_rect e2) (eval_rect e3)
        | @eval_fix _ mfix idx => f_fix
        | @eval_delta _ c decl body isdecl res cost e0 e1 => f_delta (eval_rect e1)
        | @eval_construct_App _ ind c mdecl idecl cdecl args args' cs c_as_bks e0 l a => 
            f_constr_app c_as_bks e0 l a (map_All3_dep _ (@eval_rect Γ) a)
        | @eval_construct_block _ ind c mdecl idecl cdecl args args' cs c_as_bks e0 l a =>
            f_constr_block c_as_bks e0 l a (map_All3_dep _ (@eval_rect Γ) a)
        (* | @eval_construct_block_empty _ ind c mdecl idecl cdecl e0 => f9  *)
        | @eval_prim _ p p' c ev => f_prim ev (map_eval_primitive_step_index (@eval_rect Γ) ev)
        | @eval_lazy _ t => f_lazy
        | @eval_force _ Γ' t t' v c1 c2 ev ev' => f_force (eval_rect ev) (eval_rect ev')
        end.
  End EvalInd.
  Definition eval_rec (P : WcbvFlags -> ∀ Γ t v cost, eval Γ t v cost -> Set) := @eval_rect P.
  Definition eval_ind (P : WcbvFlags -> ∀ Γ t v cost, eval Γ t v cost -> Prop) := @eval_rect P.
  Set Elimination Schemes.

End Wcbv.




Lemma eval_SI_wellformed_val {efl : EEnvFlags} {wfl : WcbvFlags} Σ Γ e v n :
  with_constructor_as_block = cstr_as_blocks ->
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
    unfold fix_env in hIn.
    revert hIn.
    remember (#|mfix|) as n eqn:heq.
    assert (
      match n with
      | 0 => True
      | S n' => n' <? #|mfix|
      end
    ).
    { destruct mfix; subst; simple; first easy.
      now rewrite /is_true Nat.ltb_lt. }
    rewrite heq in H2, H3.
    clear heq IHh_eval3.
    induction n; simple; try easy.
    intros [<- | hIn]; try easy.
    simple; unfold wf_fix, test_def; simple; repeat split; try easy.
    apply IHn; try easy; last first.
    destruct n; first easy. unfold is_true in *; rewrite ->Nat.ltb_lt in *. lia.
  - easy.

  - apply IHh_eval; first easy.
    pose proof lookup_env_wellformed wf_Σ isdecl.
    simple.

  - rewrite wellformed_mkApps in wf_e; simple.
    assert (cstr_as_blocks = false) as heq. 
    { now rewrite -cstr_blocks -(negb_involutive with_constructor_as_block) c_as_bks. }
    assert (#|args| = #|args'|).
    { revert a IHa; clear; intros a _. induction a in |- *; now simple. }
    rewrite heq in wf_e.
    rewrite /lookup_constructor_pars_args e heq; simple; repeat split; try easy; last now rewrite /is_true Nat.leb_le.
    destruct wf_e as [_ wf_e].
    revert a IHa wf_e wf_Γ; clear.
    intros a IH hwf wf_Γ.
    induction a; simple; try easy.
    destruct IH as [? ?]; simple.
    intros v [[] | hIn]; simple; try easy.
    + apply i; simple. now apply hwf.
    + apply IHa; now simple.


  - rewrite -cstr_blocks c_as_bks /lookup_constructor_pars_args e;
    rewrite -cstr_blocks c_as_bks /lookup_constructor_pars_args e in wf_e; simple.
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


Lemma eval_SI_val {efl : EEnvFlags} {wfl : WcbvFlags} Σ Γ v :
  has_tApp ->
  with_constructor_as_block = cstr_as_blocks ->
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
    eexists. exists (vConstruct ind c args'); simple; destruct cstr_as_blocks; split; try (f_equal; easy).
    + eapply eval_construct_block with (cs := extract_ns X X'); simple; try easy.
      { now assert (#|args| = ind_npars mdecl + cstr_nargs cdecl) as h by now apply eqb_eq. }
      unfold args', extract_vs, extract_ns.
      clear. funelim (extract X X'); simple; constructor; try easy.
      { now destruct a. }
      now rewrite Heq in Hind.
    + eapply eval_construct_App with (cs := extract_ns X X'); simple; try easy.
      { now rewrite cstr_blocks. }
      { now assert (#|args| <= ind_npars mdecl + cstr_nargs cdecl) as h by now apply Nat.leb_le. }
      unfold args', extract_vs, extract_ns.
      clear. funelim (extract X X'); simple; constructor; try easy.
      { now destruct a. }
      now rewrite Heq in Hind.
  - exists 0, (vClos na (fold_left (λ b t, csubst t 1 b) (map term_of_val env) b) Γ); split; simple; try constructor.
    f_equal.
    unshelve epose proof closed_fold_left_csubst 1 b (map term_of_val env) _ _ as h.
    { simple; intros ? (x & <- & hIn)%in_map_iff n.
      now eapply wellformed_closed, wellformed_val_wellformed. }
    { simple. now eapply wellformed_closed. }
    revert h. clear.
    induction Γ; simple; first reflexivity; intros h.
    rewrite csubst_closed; now simple.
  - exists 0, 
    (vRecClos (map (fold_left (λ (b0 : def term) (t0 : term), map_def (csubst t0 #|b|) b0) (map term_of_val env)) b) idx Γ);
      split; simple; try constructor.
    f_equal.
    rewrite map_map_compose. apply All_map_eq; simple.
    intros x hIn; simple. 
    remember csubst as c eqn:heq; rewrite !fold_left_map_def; subst c.
    unfold map_def; simple.
    f_equal.
    unshelve epose proof closed_fold_left_csubst #|b| (dbody x) (map term_of_val env) _ _ as h.
    { simple; intros ? (? & <- & ?)%in_map_iff n.
      now eapply wellformed_closed, wellformed_val_wellformed. }
    { unfold wf_fix, test_def in h_wf; simple.
      simple. now eapply wellformed_closed. }
    revert h. clear.
    induction Γ; simple; first reflexivity; intros h.
    rewrite csubst_closed; now simple.
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
  - exists 0, (vLazy (substl (map term_of_val env) p) Γ); split; last now constructor.
    simple; f_equal.
    unfold substl.
    unshelve epose proof closed_fold_left_csubst 0 p (map term_of_val env) _ _ as h.
    { simple; intros ? (? & <- & ?)%in_map_iff n.
      now eapply wellformed_closed, wellformed_val_wellformed. }
    { simple. now eapply wellformed_closed. }
    revert h. clear.
    induction Γ; simple; first reflexivity; intros h.
    rewrite csubst_closed; now simple.
Qed.

(* TODO: Eval deterministic *)