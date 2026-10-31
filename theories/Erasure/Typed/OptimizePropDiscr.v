(** Pass that removes discrimination (matches and projections) on things in Prop.
    This uses MetaRocq's optimization but adapted to run on our environments. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure.Typed Require Import ExAst.
From MetaRocq.Erasure Require Import EOptimizePropDiscr.

Definition remove_match_on_box_constant_body Σ cst :=
  {| cst_type := cst_type cst;
     cst_body := option_map (remove_match_on_box Σ) (cst_body cst) |}.

Definition remove_match_on_box_decl Σ d :=
  match d with
  | ConstantDecl cst => ConstantDecl (remove_match_on_box_constant_body Σ cst)
  | _ => d
  end.

Lemma trans_env_fresh_global :
      forall (kn : Kernames.kername) (g : global_env),
        fresh_globals g ->
        fresh_global kn g ->
        EnvMap.EnvMap.fresh_global kn (List.map (fun d => (d.1.1, trans_global_decl d.2)) g).
Proof.
  intros kn g fg H.
  induction H.
    * constructor.
    * cbn. inversion fg;subst;cbn in *. now constructor.
Qed.

Lemma trans_env_fresh_globals Σ :
  fresh_globals Σ ->
  EnvMap.EnvMap.fresh_globals (trans_env Σ).
Proof.
  intros fg.
  induction fg.
  + constructor.
  + cbn. constructor;auto.
    now apply trans_env_fresh_global.
Qed.

Program Definition remove_match_on_box_env (Σ : global_env) (fgΣ : fresh_globals Σ) : global_env :=
  List.map (MRProd.on_snd (remove_match_on_box_decl (EEnvMap.GlobalContextMap.make (trans_env Σ) _))) Σ.
Next Obligation.
  now apply trans_env_fresh_globals.
Qed.

Lemma trans_env_remove_match_on_box_env Σ fgΣ :
  trans_env (remove_match_on_box_env Σ fgΣ) =
  EOptimizePropDiscr.remove_match_on_box_env (EEnvMap.GlobalContextMap.make (trans_env Σ) (trans_env_fresh_globals _ fgΣ)).
Proof.
  unfold trans_env.
  unfold EOptimizePropDiscr.remove_match_on_box_env.
  unfold remove_match_on_box_env.
  unfold MRProd.on_snd. cbn.
  rewrite !List.map_map.
  apply List.map_ext.
  intros ((kn&has_deps)&decl).
  cbn.
  f_equal.
  destruct decl; auto.
  cbn.
  now destruct o.
Qed.

Lemma remove_match_on_box_correct `{EWellformed.EEnvFlags} `{EWcbvEval.WcbvFlags} Σ fgΣ t v :
  EWcbvEval.with_constructor_as_block = false ->
  ELiftSubst.closed t = true ->
  EGlobalEnv.closed_env (trans_env Σ) = true ->
  EWellformed.wf_glob (trans_env Σ) ->
  @EWcbvEval.eval _ (trans_env Σ) t v ->
  @EWcbvEval.eval
      (EWcbvEval.disable_prop_cases _)
      (trans_env (remove_match_on_box_env Σ fgΣ))
      (remove_match_on_box (EEnvMap.GlobalContextMap.make (trans_env Σ) (trans_env_fresh_globals _ fgΣ)) t)
      (remove_match_on_box (EEnvMap.GlobalContextMap.make (trans_env Σ) (trans_env_fresh_globals _ fgΣ)) v).
Proof.
  intros ? cl_t cl_env wfg ev.
  rewrite trans_env_remove_match_on_box_env.
  remember (EEnvMap.GlobalContextMap.make _ _) as Σ0.
  unshelve eapply EOptimizePropDiscr.remove_match_on_box_correct;subst;cbn;eauto.
Qed.
