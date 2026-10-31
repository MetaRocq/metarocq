(** * Definition of programs in template-rocq, well-typed terms and provided transformations **)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Transform.
From MetaRocq.Template Require TemplateProgram.
Import TemplateProgram (template_program, wt_template_program, eval_template_program).

From MetaRocq.PCUIC Require Import PCUICAstUtils PCUICAst
    PCUICGlobalEnv PCUICTyping PCUICEtaExpand
    PCUICProgram.
From MetaRocq.TemplatePCUIC Require TemplateToPCUIC TemplateToPCUICWcbvEval
  TemplateToPCUICCorrectness TemplateToPCUICExpanded.

Import Transform TemplateToPCUIC.

(** * Translation from Template to PCUIC, directly preserves evaluation *)

Definition eval_pcuic_program (p : pcuic_program) (v : term) :=
  ∥ PCUICWcbvEval.eval p.1.(trans_env_env) p.2 v ∥.

Lemma trans_template_program_wt {cf : checker_flags} p (wtp : wt_template_program p) : wt_pcuic_program (trans_template_program p).
Proof.
  move: p wtp.
  intros [Σ t] [wfext ht].
  unfold wt_pcuic_program, trans_template_program; cbn in *.
  cbn. split. eapply TemplateToPCUICCorrectness.template_to_pcuic_env_ext in wfext. apply wfext.
  destruct ht as [T HT]. exists (trans (trans_global_env Σ) T).
  eapply (TemplateToPCUICCorrectness.template_to_pcuic_typing (Σ := Ast.Env.empty_ext Σ) []). apply wfext.
  apply HT.
Qed.

Local Obligation Tactic := idtac.

(** We kludge the normalization assumptions by parameterizing over a continuation of "what will be done to the program later" as well as what properties we'll need of it *)

Program Definition template_to_pcuic_transform {cf : checker_flags} K :
  Transform.t Ast.Env.global_env global_env_ext_map Ast.term term Ast.term term
  eval_template_program eval_pcuic_program :=
 {| name := "template to pcuic";
    pre p := ∥ wt_template_program p ∥ /\ EtaExpand.expanded_program p /\ K (trans_global (Ast.Env.empty_ext p.1)) ;
    transform p _ := trans_template_program p ;
    post p := ∥ wt_pcuic_program p ∥ /\ PCUICEtaExpand.expanded_pcuic_program p /\ K p.1;
    obseq p _ p' v v':= v' = trans p'.1 v |}.
Next Obligation.
  cbn. intros cf K p [[wtp] [etap ?]].
  split; split.
  now eapply trans_template_program_wt.
  now eapply TemplateToPCUICExpanded.expanded_trans_program in etap.
  assumption.
Qed.
Next Obligation.
  red. intros cf K [Σ t] v [[]].
  unfold eval_pcuic_program, eval_template_program.
  cbn. intros [ev].
  unshelve eapply TemplateToPCUICWcbvEval.trans_wcbvEval in ev; eauto. apply X.
  eexists; split; split; eauto.
  eapply TemplateToPCUICCorrectness.template_to_pcuic_env.
  apply X. destruct X as [wfΣ [T HT]]. apply TypingWf.typing_wf in HT. apply HT. auto.
Qed.

From MetaRocq.PCUIC Require Import PCUICExpandLets PCUICExpandLetsCorrectness.

(** Expansion of let bindings in constructor types / case branches.
    Direcly preserves evaluation as well: the new value is simply the
    expansion of the old one, which is the identiy on normal forms.
*)

Program Definition pcuic_expand_lets_transform {cf : checker_flags} K :
  self_transform global_env_ext_map term eval_pcuic_program eval_pcuic_program :=
 {| name := "let expansion in branches/constructors";
    pre p := ∥ wt_pcuic_program p ∥ /\ PCUICEtaExpand.expanded_pcuic_program p /\ K (build_global_env_map (trans_global_env p.1.1), p.1.2) ;
    transform p hp := expand_lets_program p;
    post p := ∥ wt_pcuic_program (cf:=PCUICExpandLetsCorrectness.cf' cf) p ∥ /\ PCUICEtaExpand.expanded_pcuic_program p /\ K p.1;
    obseq p _ p' v v' := v' = PCUICExpandLets.trans v |}.
Next Obligation.
  intros cf K [Σ t] [[[wfext ht]] etap].
  cbn. split. sq. unfold build_global_env_map. unfold global_env_ext_map_global_env_ext. simpl.
  split. eapply PCUICExpandLetsCorrectness.trans_wf_ext in wfext. apply wfext.
  destruct ht as [T HT]. exists (PCUICExpandLets.trans T).
  eapply (PCUICExpandLetsCorrectness.pcuic_expand_lets Σ []) => //.
  apply wfext. apply PCUICExpandLetsCorrectness.trans_wf_ext in wfext. apply wfext.
  split; [ now eapply expanded_expand_lets_program | ].
  now apply etap.
Qed.
Next Obligation.
  red. intros cf K [Σ t] v [[]].
  unfold eval_pcuic_program.
  cbn. intros [ev]. destruct X.
  unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (Σ:=global_env_ext_map_global_env_ext Σ)) in ev; eauto.
  apply trans_wf; eauto.
  eexists; split; split; eauto.
  destruct s as [T HT]. now apply PCUICClosedTyp.subject_closed in HT.
Qed.
