(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv EWellformed EWcbvEval.
From MetaRocq.Utils Require Import bytestring MRString.
From MetaRocq.Erasure Require Import EWcbvEvalCstrsAsBlocksFixLambdaInd.
From MetaRocq.Erasure.StepIndex Require Import Tactics Utils SubstLemmas Values Primitives EvalStepIndex.
From Stdlib Require Import Relations.Relations.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.
Set Default Proof Using "Type*".

Definition PostT  : Type := relation (term * environment * nat).
Definition PostGT : Type := relation (term * environment * nat).

Section Exp_rel.
  Context {wfl : WcbvFlags}.
  Variable Σ : global_context.
  Variable val_rel : PostGT -> nat -> value -> value -> Prop.
  Variable Post : PostT.
  Variable PostG : PostGT.
    
  Definition exp_rel'
    (k : nat) 
    (p1 : term * environment) 
    (p2 : term * environment) 
    : Prop :=
      let '(t1, Γ1) := p1 in
      let '(t2, Γ2) := p2 in
      ∀ v1 n1,
      n1 <= k -> 
      eval Σ Γ1 t1 v1 n1 ->
      ∃ v2 n2,
        ∥eval Σ Γ2 t2 v2 n2∥ ∧ 
        Post (t1, Γ1, n1) (t2, Γ2, n2) ∧
        val_rel PostG (k - n1) v1 v2.

End Exp_rel.

Section Val_rel.
  Context {wfl : WcbvFlags}.
  Variable Σ : global_context.
  
  Fixpoint val_rel' (PostG : PostGT) (k : nat) (v1 v2 : value) {struct k} : Prop :=
    let fix val_rel_aux (v1 v2 : value) {struct v1} : Prop :=
      let fix Forall2_aux vs1 vs2 : Prop := 
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 =>
            val_rel_aux v1 v2 ∧ Forall2_aux vs1 vs2
        | _, _ => False
        end
      in
      match v1, v2 with
      | vBox, vBox => True
      | vConstruct i1 n1 vs1, vConstruct i2 n2 vs2 =>
          i1 = i2 ∧ n1 = n2 ∧ Forall2_aux vs1 vs2
      | vClos n1 t1 Γ1, vClos n2 t2 Γ2 =>
          match k with
          | 0 => True
          | S k =>
              ∀ (v1 v2 : value) j,
              j <= k ->
              val_rel' PostG (k - (k - j)) v1 v2 ->
              exp_rel' Σ val_rel' PostG PostG (k - (k - j)) (t1, v1::Γ1) (t2, v2::Γ2)
          end
      | vRecClos mfix1 n1 Γ1, vRecClos mfix2 n2 Γ2 =>
          match k with
          | 0 => True
          | S k =>
              ∀ t1 t2 v1 v2 j,
              j <= k -> 
              cunfold_fix mfix1 n1 = Some t1 ->
              cunfold_fix mfix2 n2 = Some t2 ->
              val_rel' PostG (k - (k - j)) v1 v2 ->
              exp_rel' Σ val_rel' PostG PostG (k - (k - j)) (t1, v1 :: fix_env mfix1 Γ1 ++ Γ1) (t2, v2:: fix_env mfix2 Γ2 ++ Γ2)
          end
      | vPrim (_; primIntModel i1), vPrim (_; primIntModel i2) => i1 = i2
      | vPrim (_; primFloatModel f1), vPrim (_; primFloatModel f2) => f1 = f2
      | vPrim (_; primStringModel s1), vPrim (_; primStringModel s2) => s1 = s2
      | vPrim (_; primArrayModel {|array_default := def1; array_value := vals1 |}), 
        vPrim (_; primArrayModel {|array_default := def2; array_value := vals2 |}) =>
          val_rel_aux def1 def2 ∧ Forall2_aux vals1 vals2
      | vPrim _, vPrim _ => False
      | vLazy t1 Γ1, vLazy t2 Γ2 =>
          match k with
          | 0 => True
          | S k =>
              ∀ j, j <= k ->
              exp_rel' Σ val_rel' PostG PostG (k - (k - j)) (t1, Γ1) (t2, Γ2) 
          end
      | _, _ => False
      end
    in
    val_rel_aux v1 v2
  .

  Definition val_rel (PostG : PostGT) (k : nat) (v1 v2 : value) : Prop :=
    match v1, v2 with
    | vBox, vBox => True
    | vConstruct i1 n1 vs1, vConstruct i2 n2 vs2 => i1 = i2 ∧ n1 = n2 ∧ Forall2 (val_rel' PostG k) vs1 vs2
    | vClos n1 t1 Γ1, vClos n2 t2 Γ2 =>
        ∀ (v1 v2 : value) j,
        j < k ->
        val_rel' PostG j v1 v2 ->
        exp_rel' Σ val_rel' PostG PostG j (t1, v1::Γ1) (t2, v2::Γ2)
    | vRecClos mfix1 n1 Γ1, vRecClos mfix2 n2 Γ2 =>
        ∀ t1 t2 v1 v2 j,
        j < k -> 
        cunfold_fix mfix1 n1 = Some t1 ->
        cunfold_fix mfix2 n2 = Some t2 ->
        val_rel' PostG j v1 v2 ->
        exp_rel' Σ val_rel' PostG PostG j (t1, v1 :: fix_env mfix1 Γ1 ++ Γ1) (t2, v2:: fix_env mfix2 Γ2 ++ Γ2)
    | vPrim p1, vPrim p2 => 
        match p1, p2 with
        | (_; primIntModel i1), (_; primIntModel i2) => i1 = i2
        | (_; primFloatModel f1), (_; primFloatModel f2) => f1 = f2
        | (_; primStringModel s1), (_; primStringModel s2) => s1 = s2
        | (_; primArrayModel {|array_default := def1; array_value := vals1 |}),  
          (_; primArrayModel {|array_default := def2; array_value := vals2 |}) =>
            val_rel' PostG k def1 def2 ∧ Forall2 (val_rel' PostG k) vals1 vals2
        | _, _ => False
        end
    | vLazy t1 Γ1, vLazy t2 Γ2 => 
        ∀ j, j < k ->
        exp_rel' Σ val_rel' PostG PostG j (t1, Γ1) (t2, Γ2) 
    | _, _ => False
    end.

  Lemma val_rel_eq (k : nat) PostG (v1 v2 : value) :
    val_rel' PostG k v1 v2 <-> val_rel PostG k v1 v2.
  Proof.
    unfold val_rel'.
    induction v1 in v2 |- *; destruct v2; destruct k as [| k];
    try match goal with
    | p : prim_val _ |- _ =>
        destruct p as [? [| | | [def2 vals2]]]
    end; simple; try easy.
    
    - split; repeat match goal with
      | |- _ -> _ => intro
      | h : _ ∧ _ |- _ => destruct h
      | |- _ => split
      end; subst; simple; try easy.
      + revert args0 H1. induction args; intros [|a' args'] H1; simple; try easy.
        constructor; simple; try easy.
        apply IHargs; try easy.
        intros. apply X; easy.
      + revert args0 H1. induction args; intros [|a' args'] H1; simple; try easy.
        inversion H1; subst; constructor; simple; try easy.
        apply IHargs; try easy.
        intros. apply X; easy.
    - split; repeat match goal with
      | |- _ -> _ => intro
      | h : _ ∧ _ |- _ => destruct h
      | |- _ => split
      end; subst; simple; try easy.
      + revert args0 H1. induction args; intros [|a' args'] H1; simple; try easy.
        constructor; simple; try easy.
        apply IHargs; try easy.
        intros. apply X; easy.
      + revert args0 H1. induction args; intros [|a' args'] H1; simple; try easy.
        inversion H1; subst; constructor; simple; try easy.
        apply IHargs; try easy.
        intros. apply X; easy.
    - split; intros.
      + assert (k - (k - j) = j) as heq by lia.
        edestruct (H v1 v2 j) with (n1 := n1) as (v3 & n3 & [heval] & hPost & h); try easy;
        now rewrite ->heq in *; repeat eexists.
      + assert (k - (k - j) = j) as heq by lia. rewrite -> heq in *.
        edestruct (H v1 v2 j) with (n1 := n1) as (v3 & n3 & [heval] & hPost & h); try easy.
    - split; intros.
      + assert (k - (k - j) = j) as heq by lia.
        edestruct (H t1 t2 v1 v2 j) with (n1 := n1) as (v3 & n3 & [heval] & hPost & h); try easy;
        now rewrite ->heq in *; repeat eexists.
      + assert (k - (k - j) = j) as heq by lia. rewrite -> heq in *.
        edestruct (H t1 t2 v1 v2 j) with (n1 := n1) as (v3 & n3 & [heval] & hPost & h); try easy.
    - inversion X as [| | | [def1 vals1] [? ?]]; subst; simple; try easy.
      split; repeat match goal with
      | |- _ -> _ => intro
      | h : _ ∧ _ |- _ => destruct h
      | |- _ => split
      end; subst; simple; try easy.
      + revert vals2 H0. clear X. induction vals1; intros [|a' args'] H1; simple; try easy.
        constructor; simple; try easy.
        apply IHvals1; try easy.
        intros. apply a; easy.
      + revert vals2 H0. clear X. induction vals1; intros [|a' args'] H1; simple; try easy.
        inversion H1; subst; constructor; simple; try easy.
        apply IHvals1; try easy.
        intros. apply a; easy.
    - inversion X as [| | | [def1 vals1] [? ?]]; subst; simple; try easy.
      split; repeat match goal with
      | |- _ -> _ => intro
      | h : _ ∧ _ |- _ => destruct h
      | |- _ => split
      end; subst; simple; try easy.
      + revert vals2 H0. clear X. induction vals1; intros [|a' args'] H1; simple; try easy.
        constructor; simple; try easy.
        apply IHvals1; try easy.
        intros. apply a; easy.
      + revert vals2 H0. clear X. induction vals1; intros [|a' args'] H1; simple; try easy.
        inversion H1; subst; constructor; simple; try easy.
        apply IHvals1; try easy.
        intros. apply a; easy.
    - split; intros.
      + assert (k - (k - j) = j) as heq by lia.
        edestruct (H j) with (v1 := v1) (n1 := n1) as (v3 & n3 & [heval] & hPost & h); try easy;
        now rewrite ->heq in *; repeat eexists.
      + assert (k - (k - j) = j) as heq by lia. rewrite -> heq in *.
        edestruct (H j) with (v1 := v1) (n1 := n1) as (v3 & n3 & [heval] & hPost & h); try easy.
  Qed.
  Hint Rewrite val_rel_eq : rw_hints.
  
  Lemma forall_val_rel_eq (k : nat) PostG (vs1 vs2 : list value) :
    Forall2 (val_rel' PostG k) vs1 vs2 <-> Forall2 (val_rel PostG k) vs1 vs2.
  Proof.
    split; induction 1; constructor; simple.
  Qed.
End Val_rel.

Opaque val_rel'.

Hint Rewrite @val_rel_eq : rw_hints.
Hint Rewrite @forall_val_rel_eq : rw_hints.
Definition exp_rel {wfl : WcbvFlags} Σ := exp_rel' Σ (val_rel Σ).



  
Section LogRelProps.

  Definition post_box_compat' Γ1 Γ2 (P : PostT) : Prop :=
    P (tBox, Γ1, 0) (tBox, Γ2, 0).
  
  Definition post_box_compat P := ∀ Γ1 Γ2, post_box_compat' Γ1 Γ2 P.
  (* 
    #[refine]
    Definition post_lambda_compat' : Prop := _.
    
    #[refine]
    Definition post_letin_compat' : Prop := _.

    #[refine]
    Definition post_app_compat' : Prop := _. *)
  
  Definition post_constr_compat' ind c args1 args2 Γ1 Γ2 ns1 ns2 (P1 P2 : PostT) : Prop :=
      Forall2 (λ '(a1, n1) '(a2, n2), P1 (a1, Γ1, n1) (a2, Γ2, n2)) (combine args1 ns2) (combine args2 ns2) ->
      P2 (tConstruct ind c args1, Γ1, list_sum ns1 + 1) (tConstruct ind c args2, Γ2, list_sum ns2 + 1).

  
  Definition post_constr_compat (P1 P2 : PostT) :=
    ∀ ind c args1 args2 Γ1 Γ2 ns1 ns2, post_constr_compat' ind c args1 args2 Γ1 Γ2 ns1 ns2 P1 P2.

  (* 
    (* #[refine]
      Definition post_case_compat' : Prop := _.


      Print term.
      #[refine]
      Definition post_proj_compat' p ind c args1 args2 e (P1 P2 : PostT) : Prop := _.  *)

    
    
    (* 
      Definition post_proj_compat' x t N y e1 rho1 x' t' N' y' e2 rho2 (P1 P2 : PostT) :=
      forall vs v1 v2 c1 c2 cout1 cout2,
        M.get y rho1 = Some (Vconstr t vs) ->
        nthN vs N = Some v1 ->
        P1 (e1, M.set x v1 rho1, c1, cout1)  (e2, M.set x' v2 rho2, c2, cout2) ->
        P2 (Eproj x t N y e1, rho1, c1 <+> one (Eproj x t N y e1), cout1 <+> one (Eproj x t N y e1))
          (Eproj x' t' N' y' e2, rho2, c2 <+> one (Eproj x' t' N' y' e2), cout2 <+> one (Eproj x t N y e1)). *)

    (* #[refine]
    Definition post_fix_compat' : Prop := _. *)

    (* Definition post_cofix_compat' : Prop := _. We don't have cofix here *)

    (* #[refine]
    Definition post_prim_compat' : Prop := _.

    #[refine]
    Definition post_lazy_compat' : Prop := _.

    #[refine]
    Definition post_force_compat' : Prop := _. *)



    (*     

    

    Definition post_case_compat_hd' x t e1 B1 rho1 x' t' e2 B2 rho2 (P1 P2 : PostT) :=
      forall c1 c2 cout1 cout2,
        P1 (e1, rho1, c1, cout1)  (e2, rho2, c2, cout2)  ->
        P2 (Ecase x ((t, e1) :: B1), rho1, c1 <+> one (Ecase x ((t, e1) :: B1)), cout1 <+> one (Ecase x ((t, e1) :: B1)))
          (Ecase x' ((t', e2) :: B2), rho2, c2 <+> one (Ecase x' ((t', e2) :: B2)), cout2 <+> one (Ecase x' ((t', e2) :: B2))).

    Definition post_case_compat_tl' x t e1 B1 rho1 x' t' e2 B2 rho2  (P1 P2 : PostT) :=
      forall c1 c2 cout1 cout2,
        P1 (Ecase x B1, rho1, c1, cout1)  (Ecase x' B2, rho2, c2, cout2) ->
        P2 (Ecase x ((t, e1) :: B1), rho1, c1, cout1) (Ecase x' ((t', e2) :: B2), rho2, c2, cout2).

    Definition post_fun_compat' B1 e1 rho1 B2 e2 rho2 (P1 P2 : PostT) :=
      forall c1 c2 cout1 cout2,
        P1 (e1, def_funs B1 B1 rho1 rho1, c1, cout1)  (e2, def_funs B2 B2 rho2 rho2, c2, cout2) ->
        P2 (Efun B1 e1, rho1, c1 <+> one (Efun B1 e1), cout1 <+> one (Efun B1 e1))
          (Efun B2 e2, rho2, c2 <+> one (Efun B2 e2), cout2 <+> one (Efun B1 e1)).

    Definition post_OOT' e1 rho1 e2 rho2 (P1 : PostT) :=
      forall c,
        c << one e1 -> P1 (e1, rho1, c, <0>) (e2, rho2, c, <0>).

    (* Definition post_zero e1 rho1 e2 rho2 (P1 : PostT) := *)
    (*   forall c,  *)
    (*     c <<_{ e1 } one e1 -> *)
    (*     P1 (e1, rho1, c) (e2, rho2, <0>). *)

    Definition post_base' x rho1 y rho2 (P1 : PostT) :=
      P1 (Ehalt x, rho1, one (Ehalt x), one (Ehalt x)) (Ehalt y, rho2, one (Ehalt y), one (Ehalt y)).

    Definition post_app_compat' x t ys rho1 x' t' ys' rho2 (P : PostT) (PG : PostGT):=
      forall xs e1 e2 rhoc1 rhoc2 fl f vs rhoc1' c1 c2 cout1 cout2,

        map_util.M.get x rho1 = Some (Vfun rhoc1 fl f) ->
        get_list ys rho1 = Some vs ->
        find_def f fl = Some (t, xs, e1) ->
        set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->

        (* for simplicity don't model the semantics of the target since it doesn't matter *)
        PG (e1, rhoc1', c1, cout1)  (e2, rhoc2, c2, cout2) ->
        P (Eapp x t ys, rho1, c1 <+> one (Eapp x t ys), cout1 <+> one (Eapp x t ys))
          (Eapp x' t' ys', rho2, c2 <+> one (Eapp x' t' ys'), cout2 <+> one (Eapp x' t' ys')).

    Definition post_letapp_compat' x f t ys e1 rho1 x' f' t' ys' e2 rho2 (P1 P2 : PostT) (PG : PostGT):=
      forall xs e_b1 v1  e_b2 v2
            rhoc1 rhoc2 fl h vs rhoc1' c1 c1' c2 c2' cout1 cout2 cout1' cout2',

        map_util.M.get f rho1 = Some (Vfun rhoc1 fl h) ->
        get_list ys rho1 = Some vs ->
        find_def h fl = Some (t, xs, e_b1) ->
        set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->
        bstep_fuel cenv rhoc1' e_b1 c1 (Res v1) cout1 ->

        (* for simplicity don't model the semantics of the target since it doesn't matter *)
        PG (e_b1, rhoc1', c1, cout1)  (e_b2, rhoc2, c2, cout2) ->
        P1 (e1, M.set x v1 rho1, c1', cout1') (e2, M.set x' v2 rho2, c2', cout2') ->
        P2 (Eletapp x f t ys e1, rho1, c1 <+> c1' <+> one (Eletapp x f t ys e1), cout1 <+> cout1' <+> one (Eletapp x f t ys e1))
          (Eletapp x' f' t' ys' e2, rho2, c2 <+> c2' <+> one (Eletapp x' f' t' ys' e2), cout2 <+> cout2' <+> one (Eletapp x' f' t' ys' e2)).

    Definition post_letapp_compat_OOT' x f t ys e1 rho1
              x' f' t' ys' e2 rho2 (P2 : PostT) (PG : PostGT):=
      forall xs e_b1  e_b2 rhoc1 rhoc2 fl h vs rhoc1' c1 c2 cout1 cout2,

        map_util.M.get f rho1 = Some (Vfun rhoc1 fl h) ->
        get_list ys rho1 = Some vs ->
        find_def h fl = Some (t, xs, e_b1) ->
        set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->

        (* for simplicity don't model the semantics of the target since it doesn't matter *)
        PG (e_b1, rhoc1', c1, cout1)  (e_b2, rhoc2, c2, cout2) ->
        P2 (Eletapp x f t ys e1, rho1, c1 <+> one (Eletapp x f t ys e1), cout1 <+> one (Eletapp x f t ys e1))
          (Eletapp x' f' t' ys' e2, rho2, c2 <+> one (Eletapp x' f' t' ys' e2), cout2 <+> one (Eletapp x' f' t' ys' e2)).


    Definition post_proj_compat (P1 P2 : PostT) :=
      forall x t N y e1 rho1 x' t' N' y' e2 rho2, post_proj_compat' x t N y e1 rho1 x' t' N' y' e2 rho2 P1 P2.

    Definition post_case_compat_hd (P1 P2 : PostT) :=
      forall x t e1 B1 rho1 x' t' e2 B2 rho2, post_case_compat_hd' x t e1 B1 rho1 x' t' e2 B2 rho2 P1 P2.

    Definition post_case_compat_tl (P1 P2 : PostT) :=
      forall x t e1 B1 rho1 x' t' e2 B2 rho2, post_case_compat_tl' x t e1 B1 rho1 x' t' e2 B2 rho2 P1 P2.

    Definition post_fun_compat (P1 P2 : PostT) :=
      forall B1 e1 rho1 B2 e2 rho2, post_fun_compat' B1 e1 rho1 B2 e2 rho2 P1 P2.

    Definition post_OOT (P1 : PostT) :=
      forall e1 rho1 e2 rho2, post_OOT' e1 rho1 e2 rho2 P1.

    Definition post_base (P1 : PostT) :=
      forall e1 rho1 e2 rho2, post_base' e1 rho1 e2 rho2 P1.

    Definition post_app_compat (P : PostT) (PG : PostGT) :=
      forall x t xs rho1 x' t' xs' rho2, post_app_compat' x t xs rho1 x' t' xs' rho2 P PG.

    Definition post_letapp_compat (P1 P2 : PostT) (PG : PostGT) :=
      forall x f t xs e1 rho1 x' f' t' ys' e2 rho2, post_letapp_compat' x f t xs e1 rho1 x' f' t' ys' e2 rho2 P1 P2 PG.

    Definition post_letapp_compat_OOT (P2 : PostT) (PG : PostGT) :=
      forall x f t xs e1 rho1 x' f' t' ys' e2 rho2, post_letapp_compat_OOT' x f t xs e1 rho1 x' f' t' ys' e2 rho2 P2 PG.

    

    *)
  *)
  
  Class Post_properties (P1 P2 : PostT) (PG : PostGT) : Prop :=
      { 
        HPost_box : post_box_compat P1;
        HPost_con : post_constr_compat P1 P2;
        (*
        HPost_proj : post_proj_compat P1 P2;
        HPost_fun : post_fun_compat P1 P2;
        HPost_case_hd : post_case_compat_hd P1 P2;
        HPost_case_tl : post_case_compat_tl P2 P2;
        HPost_app : post_app_compat P1 PG;
        HPost_letapp : post_letapp_compat P1 P2 PG;
        HPost_letapp_OOT : post_letapp_compat_OOT P1 PG;
        HPost_OOT : post_OOT P2;
        Hpost_base : post_base P2;
        HGPost : inclusion _ P1 PG  *)
        }.

  Variable Σ : global_context.
  Variable wfl : WcbvFlags.


  Lemma val_rel_monotonic (k j : nat) v1 v2 PostG :
    j <= k ->
    val_rel Σ PostG k v1 v2 ->
    val_rel Σ PostG j v1 v2.
  Proof.
    intros Hleq Hpre.
    revert v2 Hpre; induction v1; intros v2 Hpre;
    destruct v2; try (simpl; contradiction); simple; try easy.
    - simple; repeat split; try easy.
      destruct Hpre as (_ & _ & Hpre).
      induction Hpre; constructor; simple; try easy.
      now apply IHHpre.
    - inversion X as [ | | | [? ?] [? ?]]; subst; simple.
      clear X.
      destruct p0 as [? [| | | [? ?]]]; simple.
      destruct Hpre as [? Hpre]; split; simple; try easy.
      induction Hpre; constructor; simple; try easy.
      now apply IHHpre.
  Qed.

  Lemma exp_rel_monotonic (k j : nat) p1 p2 Post PostG :
    j <= k ->
    exp_rel Σ Post PostG k p1 p2 ->
    exp_rel Σ Post PostG j p1 p2.
  Proof.
    unfold exp_rel in *.
    destruct p1 as [e1 Γ1], p2 as [e2 Γ2].
    intros Hleq Hpre v1 n1 n1_lt_j e1_eval_v1.
    unshelve epose proof (Hpre _ _ _ e1_eval_v1) as (v2 & n2 & e2_eval_v2 & post & v1_rel_v2); first lia.
    exists v2, n2. repeat (split; try easy).
    now eapply val_rel_monotonic; last eassumption.
  Qed.

  Lemma loc_inv_monotone k p1 p2 Post Post' PostG :
    (∀ r1 r2, Post r1 r2 -> Post' r1 r2) ->
    exp_rel Σ Post PostG k p1 p2 ->
    exp_rel Σ Post' PostG k p1 p2
  .
  Proof.
    destruct p1 as [e1 Γ1], p2 as [e2 Γ2]; simple.
    intros hinc h v1 n1 n1_lt_k heval.
    destruct (h v1 n1 n1_lt_k heval) as (v2 & n2 & heval2 & hPost & hval_rel).
    now exists v2, n2.
  Qed.




  Lemma val_rel_refl (k : nat) PG v:
    val_rel Σ PG k v v.
  Proof.
    induction k as [[|k] IH] in v |- * using strong_nat_ind;
    induction v; try now simple.
    - inversion X as [| | | [? ?] [? ?]]; subst; now simple.
    - intros v1 v2 j j_le_Sk v1_rel_v2 v' n1 n1_le_j h_eval.
      repeat econstructor; simple; try easy.
      + admit.
      + admit.
    - intros v1 v2 j j_le_Sk v1_rel_v2 v' n1 n1_le_j h_eval.
      repeat econstructor; simple; try easy.
      + admit.
      + admit.
    - inversion X as [| | | [? ?] [? ?]]; subst; now simple.
    - intros j j_le_Sk v n1 n1_le_j h_eval.
      repeat econstructor; simple; try easy.
      admit.
  Abort. 

  Variable Post : PostT.
  Variable PostG : PostGT.
  Variable Hprops : Post_properties Post Post PostG.

  Lemma exp_rel_refl k e Γ Γ' : 
    Forall2 (val_rel Σ PostG k) Γ Γ' ->
    exp_rel Σ Post PostG k (e, Γ) (e, Γ').
  Proof.
    induction k as [k IH] in e, Γ, Γ', Post, Hprops |- * using strong_nat_ind.
    induction e in Γ, Γ', k, IH, Hprops |- * using EInduction.term_forall_list_ind; intros Γ_rel_Γ' v1 n1 n1_le_k h_eval;
      inversion h_eval; subst; try my_discr.
    - repeat econstructor.
      apply Hprops.
    - pose proof Forall2_nth_error_Some_l _ _ _ _ _ _ _ H0 Γ_rel_Γ' as (v2 & heq & v1_rel_v2).
      exists v2, 0; repeat split.
      + now constructor.
      + (* Need compatibility conditions on Post and PostG *) admit.
      + now rewrite Nat.sub_0_r.
    - exists (vClos n e Γ'), 0; repeat split.
      + constructor.
      + admit.
      + rewrite Nat.sub_0_r.
        intros v1 v2 j j_lt_k v1_rel_v2 v' n' n'_le_j h_eval'.
        unshelve epose proof IH j _ _ _ e (v1::Γ) (v2::Γ') _ v' n' n'_le_j h_eval' as (? & ? & [?] & ? & ?); try easy.
        { constructor; simple.
          eapply List.Forall2_impl; last eassumption.
          intros. now eapply val_rel_monotonic; last eassumption. }
        do 2 eexists; simple; repeat split; try easy.
        admit.
    - unshelve epose proof IHe1 _ _ _ _ _ Γ_rel_Γ' _ _ _ X
        as (v_e1' & c1' & [e1_eval_v_e1'] & hpost & b0'_rel_v_e1'); try easy.
      unshelve epose proof IHe2 _ (k - c1) _ (b0' :: Γ) (v_e1' :: Γ') _ _ _ _ X0 
        as (v_e2' & c2' & [e2_eval_v_e2'] & hpost2 & v1_rel_v_e2'); try easy.
      { constructor; simple. eapply List.Forall2_impl; last eassumption.
        intros. now eapply val_rel_monotonic; last eassumption. }
      exists v_e2', (c1' + c2' + 1); repeat split.
      + now econstructor.
      + admit.
      + now eapply val_rel_monotonic; last eassumption.
    - unshelve epose proof IHe1 _ k _ _ _ Γ_rel_Γ' _ _ _ X
        as ([| | | | |] & c1' & [e1_eval_v_e1'] & hpost & b0'_rel_v_e1'); try easy.
      unshelve epose proof IHe2 _ _ _ _ _ Γ_rel_Γ' _ _ _ X0
        as (v_e2' & c2' & [e2_eval_v_e2'] & hpost2 & v1_rel_v_e2'); try easy.
      repeat econstructor; try easy.
      admit.
    - unshelve epose proof IHe1 _ k _ _ _ Γ_rel_Γ' _ _ _ X
        as ([| | na' b' Γ'0' | | |] & c1' & [e1_eval_v_e1'] & hpost & b0'_rel_v_e1'); try easy.
      unshelve epose proof IHe2 _ _ _ _ _ Γ_rel_Γ' _ _ _ X0
        as (v_e2' & c2' & [e2_eval_v_e2'] & hpost2 & v1_rel_v_e2'); try easy.
      assert (val_rel' Σ PostG (min (k - c1 - 1) (k - c2)) a' v_e2') as h
      by now simple; eapply val_rel_monotonic; last eassumption.
      unshelve epose proof b0'_rel_v_e1' a' v_e2' _ _ h _ _ _ X1 as (v2 & ? & [?] & ? & ?); try lia.
      exists v2. eexists; repeat split.
      + now eapply eval_beta.
      + admit.
      + simple.
        now eapply val_rel_monotonic; try eassumption.
    - admit.
    - admit.
    - repeat eexists.
      + now econstructor.
      + admit.
      + admit.
    - admit.
    - assert (∃ args'' cs', Forall3 (eval Σ Γ') args args'' cs').
      { induction args.
        - repeat eexists; constructor.
        - destruct IHargs; try easy. all: admit. }
       repeat eexists.
      + econstructor; try easy.
        induction args.
        * constructor. 
        * admit. 
      + admit.
      + admit.
    - admit.
    - admit.
    - exists (vRecClos m n Γ'), 0.
      repeat split.
      + constructor.
      + admit.
      + repeat intro.
  Admitted.

End LogRelProps.

