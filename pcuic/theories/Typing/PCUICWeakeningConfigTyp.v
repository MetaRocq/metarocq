(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils MRUtils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICEquality PCUICContextSubst PCUICUnivSubst PCUICCases
  PCUICReduction PCUICCumulativity PCUICTyping PCUICGuardCondition
  PCUICWeakeningConfig PCUICWeakeningConfigConv.
From Equations Require Import Equations.

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

Local Ltac constructor_per_goal' _ :=
  let n := numgoals in
  [ > .. | econstructor n; shelve ];
  gtry (constructor_per_goal' ()).
Local Ltac constructor_per_goal _ :=
  unshelve constructor_per_goal' (); shelve_unifiable.

Lemma weakening_config_wf_local_sized {cf1 cf2 : checker_flags} Σ Γ
  (Hwf :  All_local_env (lift_typing (@typing cf1) Σ) Γ)
  (IH : forall Γ0 t0 T0 (H0 : @typing cf1 Σ Γ0 t0 T0),
      typing_size H0 < S (All_local_env_size (fun _ _ _ H => typing_size H) Γ Hwf)
      -> @typing cf2 Σ Γ0 t0 T0)
  : wf_local Σ Γ.
Proof.
  simpl in *.
  induction Hwf; [ constructor 1 | constructor 2 | constructor 3 ].
  2,4: eapply @lift_typing_size_impl with (Psize := @typing_size _ _ _) (tu := t0); unfold lift_sorting_size; cbn; intros.
  all: try (unshelve eapply IH; [ eassumption | ];
            try solve [ constructor; simpl in *; cbn in *; lia ]).
  all: repeat (exactly_once (idtac; multimatch goal with H : _ |- _ => unshelve eapply H; [ try eassumption .. | intros; simpl in * ]; clear H end)).
  all: try (cbn; lia).
Qed.

Lemma weakening_config {cf1 cf2} Σ Γ t T :
  config.impl cf1 cf2 ->
  @typing cf1 Σ Γ t T ->
  @typing cf2 Σ Γ t T.
Proof.
  intros Hcf H.
  pose proof (@Fix_F { Σ & { Γ & { t & { T & @typing cf1 Σ Γ t T }}}}) as p0.
  specialize (p0 (PCUICUtils.dlexprod (precompose lt (fun Σ => globenv_size (fst Σ)))
                    (fun Σ => precompose lt (fun x => typing_size x.π2.π2.π2)))) as p.
  try clear p0.
  set (foo := (Σ; Γ; t; _; H) : { Σ & { Γ & { t & { T & Σ ;;; Γ |- t : T }}}}).
  change Σ with foo.π1.
  change Γ with foo.π2.π1.
  change t with foo.π2.π2.π1.
  change T with foo.π2.π2.π2.π1.
  change H with foo.π2.π2.π2.π2.
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p; [ | apply p; apply PCUICUtils.wf_dlexprod; intros; apply wf_precompose; apply lt_wf].
  clear p.
  clear Σ Γ t T H.
  intros (Σ & Γ & t & T & H). simpl.
  intros IH. specialize (fun Σ Γ t T H => IH (Σ; Γ; t; T; H)). simpl in IH.
  destruct H; constructor_per_goal (); try eassumption.
  5:destruct p1; constructor; eauto; solve_all.
  all: try (unshelve eapply IH; [ eassumption .. | ];
            try solve [ constructor; simpl; lia ]).
  all: try (eapply (@weakening_config_cumulSpec cf1 cf2); eassumption).
  all: try now constructor; simpl; repeat destruct ?; simpl; lia.
  all: specialize (fun Γ t T H H' => IH _ Γ t T H ltac:(right; exact H')).
  all: simpl in IH.
  all: try (set (k := fix_context _) in *; clearbody k).
  all: match goal with
       | [ H : lift_typing0 _ ?j |- lift_typing0 _ ?j ]
         => eapply @lift_typing_size_impl with (Psize := @typing_size _ _ _) (tu := H); unfold lift_sorting_size, on_def_type_sorting_size in *; cbn; intros
       | [ H : All (on_def_type _ _) ?l |- All (on_def_type _ _) ?l ]
         => is_var l; clear -H IH; induction H as [|???? IH']; constructor;
            [eapply @lift_typing_size_impl with (Psize := @typing_size _ _ _) (tu := p); unfold lift_sorting_size, on_def_type_sorting_size in *; cbn; intros|]
       | [ H : All (on_def_body _ _ _) ?l |- All (on_def_body _ _ _) ?l ]
         => is_var l; clear -H IH; induction H as [|???? IH']; constructor;
            [eapply @lift_typing_size_impl with (Psize := @typing_size _ _ _) (tu := p); unfold lift_sorting_size, on_def_body_sorting_size in *; cbn; intros|]
       | [ H : case_side_conditions _ _ _ _ _ _ _ _ _ _ _ |- case_side_conditions _ _ _ _ _ _ _ _ _ _ _ ] => destruct H; constructor
       | [ H : case_branch_typing _ _ _ _ _ _ _ _ _ _ |- case_branch_typing _ _ _ _ _ _ _ _ _ _ ] => destruct H; constructor
       | _ => idtac
       end.
  all: unfold wf_branches in *.
  all: repeat match goal with H : All _ (_ :: _) |- _ => depelim H end.
  all: rdest.
  all: try (unshelve eapply IH'; clear IH'; auto; [];
            intros;
            unshelve eapply IH; [ eassumption .. | simpl; lia ]).
  all: try (unshelve eapply IH; [ eassumption .. | simpl; lia ]).
  all: try now eapply (@weakening_config_consistent_instance cf1 cf2); eassumption.
  all: try now eapply (@weakening_config_is_allowed_elimination cf1 cf2); eassumption.
  all: try now repeat destruct ?; subst; simpl in *; assumption.
  all: repeat destruct ?; subst.
  all: lazymatch goal with
       | [ H : ctx_inst _ _ _ _ |- ctx_inst _ _ _ _ ]
         => generalize dependent H;
            repeat match goal with
              | [ |- context[typing_size ?x] ]
                => generalize (typing_size x); clear x; intro
              end;
            intro H; intros;
            induction H; constructor_per_goal ()
       | [ H : All2i _ _ ?x ?y |- All2i _ _ ?x ?y ]
         => induction H; constructor_per_goal (); cbv zeta in *
       | _ => idtac
       end.
  all: repeat rdest; try assumption.
  all: repeat (exactly_once (idtac; multimatch goal with H : _ |- _ => unshelve eapply H; [ try eassumption .. | intros; simpl ctx_inst_size in *; simpl branches_size in * ]; clear H end)).
  all: lazymatch goal with
       | [ |- _ < _ ] => lia || (simpl; lia)
       | _ => idtac
       end.
  all: repeat match goal with H : Forall2 _ (_ :: _) (_ :: _) |- _ => depelim H end.
  all: try assumption.
  2:{ eapply (All_map_size (fun x H => typing_size H) _ hvalue). intros. eapply (IH _ _ _ p). lia. }
  all: [ > unshelve eapply (@weakening_config_wf_local_sized cf1 cf2); [ eassumption | ] .. ].
  all: intros; unshelve eapply IH; [ eassumption | ].
  all: simpl in *; try lia.
  all: cbn in *; try lia.
  all: try assumption.
  all: repeat match goal with
         | [ |- context[All_local_env_size ?x ?y ?w] ]
           => let v := fresh in
              set (v := All_local_env_size _ y w) in *
         end.
  all: try lia.
Qed.

Lemma weakening_config_wf_local {cf1 cf2 : checker_flags} Σ Γ :
  config.impl cf1 cf2
  -> match cf1 with _ => wf_local Σ Γ end
  -> match cf2 with _ => wf_local Σ Γ end.
Proof.
  intros Hcf H; eapply All_local_env_impl; [ eassumption | cbn ].
  intros * H'; eapply lift_typing_impl; [ eassumption | ].
  intros *; eapply (@weakening_config cf1 cf2); assumption.
Qed.

Lemma weakening_config_wf {cf1 cf2 : checker_flags} Σ :
  config.impl cf1 cf2
  -> @wf cf1 Σ
  -> @wf cf2 Σ.
Proof.
  rewrite /wf.
  intros; eapply (@on_global_env_impl_config cf1 cf2); try eassumption; cbn.
  { intros; eapply @lift_typing_impl; [ eassumption | ].
    intros; eapply (@weakening_config cf1 cf2); eassumption. }
  { intros; eapply (@weakening_config_cumulSpec0 cf1 cf2); eassumption. }
Qed.
