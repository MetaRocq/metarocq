From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames uGraph.
From MetaRocq.Erasure Require Import EGlobalEnv ErasureFunction.
From MetaRocq.Erasure Require Import EAstUtils EArities Extract Prelim EDeps ErasureProperties ErasureCorrectness.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICSafeReduce PCUICSafeRetyping PCUICRetypingEnvIrrelevance.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive
  PCUICReduction PCUICReflect PCUICWeakeningEnv PCUICWeakeningEnvTyp PCUICCasesContexts
  PCUICWeakeningConv PCUICWeakeningTyp PCUICContextConversionTyp PCUICTyping PCUICGlobalEnv PCUICInversion PCUICGeneration
  PCUICConfluence PCUICConversion PCUICUnivSubstitutionTyp PCUICCumulativity PCUICSR PCUICSafeLemmata PCUICNormalization
  PCUICValidity PCUICPrincipality PCUICElimination PCUICOnFreeVars PCUICWellScopedCumulativity PCUICSN PCUICEtaExpand.

(* Σ is a fragment of Σ' if every lookup in Σ gives the same result as Σ' *)
Definition eglobal_env_fragment Σ Σ' :
  (forall kn decl, lookup_env Σ kn = Some decl -> lookup_env Σ' kn = Some decl).

(* we use the [match] trick to get typeclass resolution to pick up the right instances without leaving any evidence in the resulting term, and without having to pass them manually everywhere *)
Abbreviation NormalizationIn_erase_global_decls X decls
  := (match extraction_checker_flags, extraction_normalizing return _ with
      | cf, no
        => forall n,
          n < List.length decls ->
          let X' := iter abstract_pop_decls (S n) X in
          forall kn cb pf,
            List.hd_error (List.skipn n decls) = Some (kn, ConstantDecl cb) ->
            let Xext := abstract_make_wf_env_ext X' (cst_universes cb) pf in
            forall Σ, wf_ext Σ -> Σ ∼_ext Xext -> NormalizationIn Σ
      end)
       (only parsing).

Program Fixpoint erase_global
  {X_type : abstract_env_impl} (X : X_type.π1) (decls : global_declarations)
  {normalization_in : NormalizationIn_erase_global_decls X decls}
  (prop : forall Σ : global_env, abstract_env_rel X Σ -> Σ.(declarations) = decls)
  : E.global_declarations :=
  match decls with
  | [] => []
  | (kn, ConstantDecl cb) :: decls =>
    let X' := abstract_pop_decls X in
    let Xext := abstract_make_wf_env_ext X' (cst_universes cb) _ in
    let normalization_in' : @id Prop _ := _ in (* hack to avoid program erroring out on unresolved tc *)
    let cb' := @erase_constant_body X_type Xext normalization_in' cb _ in
    let X'' := erase_global X' decls _ in
    ((kn, E.ConstantDecl (fst cb')) :: X'')
  | (kn, InductiveDecl mib) :: decls =>
    let X' := abstract_pop_decls X in
    let mib' := erase_mutual_inductive_body mib in
    let X'' := erase_global X' decls _ in
    ((kn, E.InductiveDecl mib') :: X'')

  end.
Next Obligation.
  pose proof (abstract_env_wf _ H) as [wf].
  pose proof (abstract_env_exists X) as [[? HX]].
  pose proof (abstract_env_wf _ HX) as [wfX].
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  destruct (abstract_pop_decls_correct X decls prop' _ _ HX H) as [? []].
  clear H. specialize (prop _ HX). destruct x, Σ, H0; cbn in *.
  subst. sq. destruct wfX. depelim o0. destruct o1.  split => //.
Qed.
Next Obligation.
  cbv [id].
  unshelve eapply (normalization_in 0); cbn; try reflexivity; try lia.
Defined.
Next Obligation.
  pose proof (abstract_env_ext_wf _ H) as [wf].
  pose proof (abstract_env_exists (abstract_pop_decls X)) as [[? HX']].
  pose proof (abstract_env_wf _ HX') as [wfX'].
  pose proof (abstract_env_exists X) as [[? HX]].
  pose proof (abstract_env_wf _ HX) as [wfX].
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  pose proof (abstract_pop_decls_correct X decls prop' _ _ HX HX') as [? []].
  pose proof (abstract_make_wf_env_ext_correct _ _ _ _ _ HX' H).
  clear H HX'. specialize (prop _ HX). destruct x, Σ as [[] u], H0; cbn in *.
  subst. sq. inversion H3. subst. clear H3. destruct wfX. cbn in *.
  rewrite prop in o0. depelim o0. destruct o1. exact on_global_decl_d.
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
  pose proof (abstract_env_exists X) as [[? HX]].
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
pose proof (abstract_env_exists X) as [[? HX]].
assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
{ now eexists. }
now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
  pose proof (abstract_env_exists X) as [[? HX]].
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
pose proof (abstract_env_exists X) as [[? HX]].
assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
{ now eexists. }
now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.



Lemma erase_global_fast_fragment
  X_type deps X decls {normalization_in} (prf:forall Σ : global_env, abstract_env_rel X Σ -> declarations Σ = decls) :
  eglobal_env_fragment
    (@ErasureFunction.erase_global_fast X_type deps X decls normalization_in prf)
    (@E)



Lemma erase_program_fst {guard : abstract_guard_impl} (p p' : pcuic_program)
  {normalization_in : PCUICTyping.wf_ext p.1 -> PCUICSN.NormalizationIn p.1}
  {normalization_in' : PCUICTyping.wf_ext p'.1 -> PCUICSN.NormalizationIn p'.1}
{normalization_in_adjust_universes : PCUICTyping.wf_ext p.1 ->
                                     PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p.1}
{normalization_in_adjust_universes' : PCUICTyping.wf_ext p'.1 ->
PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn
  p'.1} wt wt' :
p.1 = p'.1 ->
(erase_program p wt).1 = (erase_program p' wt').1.
Proof.
destruct p, p'; intros; subst. cbn in H. subst g0.
unfold erase_program.
assert (map_squash fst wt = map_squash fst wt') by apply proof_irrelevance.
rewrite -H. cbn.
epose proof ErasureFunction.erase_irrel_global_env.
Abort.Lemma erase_global_fragment Σ

