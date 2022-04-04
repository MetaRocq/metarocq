(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils Kernames.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICTyping PCUICInversion
     PCUICSafeLemmata. (* for welltyped *)
From MetaCoq.SafeChecker Require Import PCUICWfEnvImpl.
From MetaCoq.Erasure Require Import EAst EAstUtils EDeps EExtends
    ELiftSubst ECSubst EGlobalEnv EWellformed EWcbvEval Extract Prelim
    ErasureFunction EArities EProgram.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MCMonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
Require Import ssreflect ssrbool.

(** We assumes [Prop </= Type] and universes are checked correctly in the following. *)
Local Existing Instance extraction_checker_flags.

Ltac introdep := let H := fresh in intros H; depelim H.

#[global]
Hint Constructors eval : core.

Section optimize.
  Context (Σ : global_context).

  Definition is_box_fix mfix idx := 
    match nth_error mfix idx with
    | Some {| dbody := tBox |} => true
    | _ => false
    end.

  Fixpoint optimize (t : term) : term :=
    match t with
    | tRel i => tRel i
    | tEvar ev args => tEvar ev (List.map optimize args)
    | tLambda na M => tLambda na (optimize M)
    | tApp u v => tApp (optimize u) (optimize v)
    | tLetIn na b b' => tLetIn na (optimize b) (optimize b')
    | tCase ind c brs =>
      let brs' := List.map (on_snd optimize) brs in
      match EGlobalEnv.inductive_isprop_and_pars Σ (fst ind) with
      | Some (true, npars) =>
        match brs' with
        | [(a, b)] => ECSubst.substl (repeat tBox #|a|) b
        | _ => tCase ind (optimize c) brs'
        end
      | _ => tCase ind (optimize c) brs'
      end
    | tProj p c =>
      match EGlobalEnv.inductive_isprop_and_pars Σ p.1.1 with 
      | Some (true, _) => tBox
      | _ => tProj p (optimize c)
      end
    | tFix mfix idx =>
      let mfix' := List.map (map_def optimize) mfix in
      if is_box_fix mfix idx then tBox
      else tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := List.map (map_def optimize) mfix in
      tCoFix mfix' idx
    | tBox => t
    | tVar _ => t
    | tConst _ => t
    | tConstruct _ _ => t
    (* | tPrim _ => t *)
    end.

  Lemma optimize_mkApps f l : optimize (mkApps f l) = mkApps (optimize f) (map optimize l).
  Proof.
    induction l using rev_ind; simpl; auto.
    now rewrite mkApps_app /= IHl map_app /= mkApps_app /=.
  Qed.

  Lemma map_repeat {A B} (f : A -> B) x n : map f (repeat x n) = repeat (f x) n.
  Proof.
    now induction n; simpl; auto; rewrite IHn.
  Qed.
  
  Lemma map_optimize_repeat_box n : map optimize (repeat tBox n) = repeat tBox n.
  Proof. by rewrite map_repeat. Qed.

  Import ECSubst.

  Lemma csubst_mkApps {a k f l} : csubst a k (mkApps f l) = mkApps (csubst a k f) (map (csubst a k) l).
  Proof.
    induction l using rev_ind; simpl; auto.
    rewrite mkApps_app /= IHl.
    now rewrite -[EAst.tApp _ _](mkApps_app _ _ [_]) map_app.
  Qed.

  Lemma csubst_closed t k x : closedn k x -> csubst t k x = x.
  Proof.
    induction x in k |- * using EInduction.term_forall_list_ind; simpl; auto.
    all:try solve [intros; f_equal; solve_all; eauto].
    intros Hn. eapply Nat.ltb_lt in Hn.
    - destruct (Nat.compare_spec k n); try lia. reflexivity.
    - move/andP => []. intros. f_equal; solve_all; eauto.
    - move/andP => []. intros. f_equal; solve_all; eauto.
    - move/andP => []. intros. f_equal; solve_all; eauto.
      destruct x0; cbn in *. f_equal; auto.
  Qed.

  Lemma closed_optimize t k : closedn k t -> closedn k (optimize t).
  Proof.
    induction t in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - move/andP: H => [] clt cll. destruct EGlobalEnv.inductive_isprop_and_pars as [[[|] _]|] => /= //.
      destruct l as [|[br n] [|l']] eqn:eql; simpl.
      rewrite IHt //.
      depelim X. cbn in *.
      rewrite andb_true_r in cll.
      specialize (i _ cll).
      eapply closed_substl. solve_all. eapply All_repeat => //.
      now rewrite repeat_length.
      rtoProp; solve_all. depelim cll. solve_all.
      depelim cll. depelim cll. solve_all.
      depelim cll. depelim cll. solve_all.
      rtoProp; solve_all. solve_all.
      rtoProp; solve_all. solve_all.
    - destruct EGlobalEnv.inductive_isprop_and_pars as [[[|] _]|]; cbn; auto.
    - destruct is_box_fix => //.
      cbn; auto; rewrite forallb_map; len; solve_all.
  Qed.
 
  Lemma subst_csubst_comm l t k b : 
    forallb (closedn 0) l -> closed t ->
    subst l 0 (csubst t (#|l| + k) b) = 
    csubst t k (subst l 0 b).
  Proof.
    intros hl cl.
    rewrite !closed_subst //.
    rewrite distr_subst. f_equal.
    symmetry. solve_all.
    rewrite subst_closed //.
    eapply closed_upwards; tea. lia. 
  Qed.

  Lemma substl_subst s t : 
    forallb (closedn 0) s ->
    substl s t = subst s 0 t.
  Proof.
    induction s in t |- *; cbn; auto.
    intros _. now rewrite subst_empty.
    move/andP=> []cla cls.
    rewrite (subst_app_decomp [_]).
    cbn. rewrite lift_closed //.
    rewrite closed_subst //. now eapply IHs.
  Qed.

  Lemma substl_csubst_comm l t k b : 
    forallb (closedn 0) l -> closed t ->
    substl l (csubst t (#|l| + k) b) = 
    csubst t k (substl l b).
  Proof.
    intros hl cl.
    rewrite substl_subst //.
    rewrite substl_subst //.
    apply subst_csubst_comm => //.
  Qed.

  (* Lemma is_box_fix_csubst a m n k : is_box_fix m n = is_box_fix (map (map_def (csubst a (#|m| + k))) m) n.
  Proof.
    unfold is_box_fix. rewrite nth_error_map. destruct nth_error as [[]|] => /=.
     *)
  Import EEtaExpanded.
  Ltac solve_discr' := try solve_discr; repeat solve_discr_args; try congruence.

  Lemma optimize_csubst {efl : EEnvFlags} a k i b : 
    closed a ->
    wellformed Σ i b ->
    optimize (ECSubst.csubst a k b) = ECSubst.csubst (optimize a) k (optimize b).
  Proof.
    induction b in i, k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros cl exp; try easy; 
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold test_def in *;
    simpl closed in *; try solve [depelim exp; try solve_discr'; simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - destruct (k ?= n)%nat; auto.
    - depelim exp.
      * destruct args using rev_case; try congruence.
        rewrite mkApps_app in H2. noconf H2.
        eapply Forall_app in H1 as []. depelim H2.
        f_equal; eauto. eapply IHb1; eauto. eapply expanded_mkApps_expanded; eauto; solve_all.
      * destruct args using rev_case; try congruence. solve_discr.
        rewrite mkApps_app in H2. noconf H2.
        eapply Forall_app in H1 as []. depelim H2.
        rewrite !csubst_mkApps /= !optimize_mkApps /=.
        rewrite !csubst_mkApps /=. f_equal; eauto. f_equal. solve_all.
        f_equal; eauto. eapply IHb1; eauto.
         eapply expanded_mkApps_expanded; eauto; solve_all.

      *
         eauto.
      eapply IHb1. auto.
    - unfold on_snd; cbn.
      destruct EGlobalEnv.inductive_isprop_and_pars as [[[|] _]|] => /= //.
      destruct l as [|[br n] [|l']] eqn:eql; simpl.
      * f_equal; auto.
      * depelim X. simpl in *.
        rewrite e //.
        assert (#|br| = #|repeat tBox #|br| |). now rewrite repeat_length.
        rewrite {2}H0.
        rewrite substl_csubst_comm //.
        solve_all. eapply All_repeat => //.
        now eapply closed_optimize.
      * depelim X. depelim X.
        f_equal; eauto. f_equal; eauto.
        f_equal; eauto.
        f_equal; eauto. f_equal; eauto.
        rewrite map_map_compose; solve_all.
      * rewrite ?map_map_compose; f_equal; eauto; solve_all.
      * rewrite ?map_map_compose; f_equal; eauto; solve_all.
    - destruct EGlobalEnv.inductive_isprop_and_pars as [[[|] _]|]=> //;
      now rewrite IHb.
    - rewrite  !nth_error_map.
      destruct nth_error => /= //.

  Qed.

  Lemma optimize_substl s t : 
    forallb (closedn 0) s ->
    optimize (substl s t) = substl (map optimize s) (optimize t).
  Proof.
    induction s in t |- *; simpl; auto.
    move/andP => [] cla cls.
    rewrite IHs //. f_equal.
    now rewrite optimize_csubst.
  Qed.

  Lemma optimize_iota_red pars args br :
    forallb (closedn 0) args ->
    optimize (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map optimize args) (on_snd optimize br).
  Proof.
    intros cl.
    unfold EGlobalEnv.iota_red.
    rewrite optimize_substl //.
    rewrite forallb_rev forallb_skipn //.
    now rewrite map_rev map_skipn.
  Qed.
  
  Lemma optimize_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def optimize) mfix) = map optimize (EGlobalEnv.fix_subst mfix).
  Proof.
    unfold EGlobalEnv.fix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def optimize) mfix) = map optimize (EGlobalEnv.cofix_subst mfix).
  Proof.
    unfold EGlobalEnv.cofix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cunfold_fix mfix idx n f : 
    forallb (closedn 0) (EGlobalEnv.fix_subst mfix) ->
    cunfold_fix mfix idx = Some (n, f) ->
    cunfold_fix (map (map_def optimize) mfix) idx = Some (n, optimize f).
  Proof.
    intros hfix.
    unfold cunfold_fix.
    rewrite nth_error_map.
    destruct nth_error.
    intros [= <- <-] => /=. f_equal.
    now rewrite optimize_substl // optimize_fix_subst.
    discriminate.
  Qed.

  Lemma optimize_cunfold_cofix mfix idx n f : 
    forallb (closedn 0) (EGlobalEnv.cofix_subst mfix) ->
    cunfold_cofix mfix idx = Some (n, f) ->
    cunfold_cofix (map (map_def optimize) mfix) idx = Some (n, optimize f).
  Proof.
    intros hcofix.
    unfold cunfold_cofix.
    rewrite nth_error_map.
    destruct nth_error.
    intros [= <- <-] => /=. f_equal.
    now rewrite optimize_substl // optimize_cofix_subst.
    discriminate.
  Qed.

  Lemma optimize_nth {n l d} : 
    optimize (nth n l d) = nth n (map optimize l) (optimize d).
  Proof.
    induction l in n |- *; destruct n; simpl; auto.
  Qed.

End optimize.

Lemma is_box_inv b : is_box b -> ∑ args, b = mkApps tBox args.
Proof.
  unfold is_box, EAstUtils.head.
  destruct decompose_app eqn:da.
  simpl. destruct t => //.
  eapply decompose_app_inv in da. subst.
  eexists; eauto.
Qed.

Lemma eval_is_box {wfl:WcbvFlags} Σ t u : Σ ⊢ t ▷ u -> is_box t -> u = EAst.tBox.
Proof.
  intros ev; induction ev => //.
  - rewrite is_box_tApp.
    intros isb. intuition congruence.
  - rewrite is_box_tApp. move/IHev1 => ?; solve_discr.
  - rewrite is_box_tApp. move/IHev1 => ?; solve_discr.
  - rewrite is_box_tApp. move/IHev1 => ?. subst => //.
  - rewrite is_box_tApp. move/IHev1 => ?. subst. cbn in i.
    destruct EWcbvEval.with_guarded_fix => //.
  - destruct t => //.
Qed. 

Lemma isType_tSort {cf:checker_flags} {Σ : global_env_ext} {Γ l A} {wfΣ : wf Σ} : Σ ;;; Γ |- tSort (Universe.make l) : A -> isType Σ Γ (tSort (Universe.make l)).
Proof.
  intros HT.
  eapply inversion_Sort in HT as [l' [wfΓ Hs]]; auto.
  eexists; econstructor; eauto.
Qed.

Lemma isType_it_mkProd {cf:checker_flags} {Σ : global_env_ext} {Γ na dom codom A} {wfΣ : wf Σ} :   
  Σ ;;; Γ |- tProd na dom codom : A -> 
  isType Σ Γ (tProd na dom codom).
Proof.
  intros HT.
  eapply inversion_Prod in HT as (? & ? & ? & ? & ?); auto.
  eexists; econstructor; eauto.
Qed.

Import ErasureCorrectness.

Lemma erasable_tBox_value (wfl := Ee.default_wcbv_flags) (Σ : global_env_ext) (wfΣ : wf_ext Σ) t T v :
  forall wt : Σ ;;; [] |- t : T,
  Σ |-p t ▷ v -> erases Σ [] v tBox -> ∥ isErasable Σ [] t ∥.
Proof.
  intros.
  depind H.
  eapply Is_type_eval_inv; eauto. eexists; eauto.
Qed.

Lemma erase_eval_to_box (wfl := Ee.default_wcbv_flags) {Σ : wf_env} {univs wfext t v Σ' t' deps} :
  let Σext := make_wf_env_ext Σ univs wfext in
  forall wt : ∀ Σ0 : global_env_ext, abstract_env_rel' Σext Σ0 →  welltyped Σ0 [] t,
  erase Σext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global deps Σ = Σ' ->
  PCUICWcbvEval.eval Σ t v ->
  @Ee.eval Ee.default_wcbv_flags Σ' t' tBox -> ∥ isErasable Σext [] t ∥.
Proof.
  intros Σext wt.
  intros.
  destruct (erase_correct Σ univs wfext _ _ _ _ _ wt H H0 H1 X) as [ev [eg [eg']]].
  pose proof (Ee.eval_deterministic H2 eg'). subst.
  destruct wfext. destruct (wt _ eq_refl) as [T wt'].
  eapply erasable_tBox_value; eauto.
Qed.

Definition optimize_constant_decl Σ cb := 
  {| cst_body := option_map (optimize Σ) cb.(cst_body) |}.
  
Definition optimize_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (optimize_constant_decl Σ cb)
  | InductiveDecl idecl => d
  end.

Fixpoint optimize_env (Σ : EAst.global_declarations) := 
  match Σ with
  | [] => []
  | d :: Σ => on_snd (optimize_decl Σ) d :: optimize_env Σ
  end.

Import EGlobalEnv EExtends.

(* Lemma extends_is_propositional {Σ Σ'} : 
  wf_glob Σ' -> extends Σ Σ' ->
  forall ind, 
  match inductive_isprop_and_pars Σ ind with
  | Some b => inductive_isprop_and_pars Σ' ind = Some b
  | None => inductive_isprop_and_pars Σ' ind = None
  end.
Proof.
  intros wf ex ind.
  rewrite /inductive_isprop_and_pars.
  destruct lookup_env eqn:lookup => //.
  now rewrite (extends_lookup wf ex lookup).

Qed. *)

Lemma extends_inductive_isprop_and_pars {efl : EEnvFlags} {Σ Σ' ind} : extends Σ Σ' -> wf_glob Σ' ->
  isSome (lookup_inductive Σ ind) -> 
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars Σ' ind.
Proof.
  intros ext wf; cbn.
  unfold inductive_isprop_and_pars.
  destruct lookup_env as [[]|] eqn:hl => //.
  rewrite (extends_lookup wf ext hl).
  destruct nth_error => //.
Qed.

Lemma wellformed_optimize_extends {wfl: EEnvFlags} Σ t : 
  forall n, EWellformed.wellformed Σ n t ->
  forall Σ', extends Σ Σ' -> wf_glob Σ' ->
  optimize Σ t = optimize Σ' t.
Proof.
  induction t using EInduction.term_forall_list_ind; cbn -[lookup_constant lookup_inductive]; intros => //.
  all:rtoProp; intuition auto.  
  all:f_equal; eauto; solve_all.
  - assert (map (on_snd (optimize Σ)) l = map (on_snd (optimize Σ')) l) as -> by solve_all.
    rewrite (extends_inductive_isprop_and_pars H0 H1 H2).
    destruct inductive_isprop_and_pars as [[[]]|].
    destruct map => //. f_equal; eauto.
    destruct l0 => //. destruct p0 => //. f_equal; eauto.
    all:f_equal; eauto; solve_all.
  - rewrite (extends_inductive_isprop_and_pars H0 H1 H3).
    destruct inductive_isprop_and_pars as [[[]]|] => //.
    all:f_equal; eauto.
Qed.

Lemma wellformed_optimize_decl_extends {wfl: EEnvFlags} Σ t : 
  wf_global_decl Σ t ->
  forall Σ', extends Σ Σ' -> wf_glob Σ' ->
  optimize_decl Σ t = optimize_decl Σ' t.
Proof.
  destruct t => /= //.
  intros wf Σ' ext wf'. f_equal. unfold optimize_constant_decl. f_equal.
  destruct (cst_body c) => /= //. f_equal.
  now eapply wellformed_optimize_extends.
Qed.
  

Lemma lookup_env_optimize_env_Some {efl : EEnvFlags} Σ kn d : 
  wf_glob Σ ->
  lookup_env Σ kn = Some d ->
  ∑ Σ', extends Σ' Σ × wf_global_decl Σ' d × (lookup_env (optimize_env Σ) kn) = Some (optimize_decl Σ' d).
Proof.
  induction Σ; simpl; auto => //.
  intros wf.
  case: eqb_specT => //.
  - intros ->. cbn. intros [= <-]. exists Σ. split. now eexists [_]. split => //.
    now depelim wf.
  - intros _. forward IHΣ. now depelim wf.
    intros hl. specialize (IHΣ hl) as [Σ' [[Σ'' ext] eq]].
    subst Σ. exists Σ'. split => //. now exists (a :: Σ'').
Qed.

Lemma lookup_env_optimize_env_None {efl : EEnvFlags} Σ kn : 
  lookup_env Σ kn = None ->
  lookup_env (optimize_env Σ) kn = None.
Proof.
  induction Σ; simpl; auto => //.
  case: eqb_specT => //.
Qed.

Lemma lookup_env_optimize {efl : EEnvFlags} Σ kn : 
  wf_glob Σ ->
  lookup_env (optimize_env Σ) kn = option_map (optimize_decl Σ) (lookup_env Σ kn).
Proof.
  intros wf.
  destruct (lookup_env Σ kn) eqn:hl.
  - eapply lookup_env_optimize_env_Some in hl as [Σ' [ext [wf' hl']]] => /=.
    rewrite hl'. f_equal.
    eapply wellformed_optimize_decl_extends; eauto. auto.
    
  - cbn. now eapply lookup_env_optimize_env_None in hl. 
Qed.

Lemma is_propositional_optimize {efl : EEnvFlags} Σ ind : 
  wf_glob Σ ->
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars (optimize_env Σ) ind.
Proof.
  rewrite /inductive_isprop_and_pars => wf.
  rewrite (lookup_env_optimize Σ (inductive_mind ind) wf).  
  case: lookup_env => [[decl|]|] => //.
Qed.

Lemma closed_iota_red pars c args brs br :
  forallb (closedn 0) args ->
  nth_error brs c = Some br ->
  #|skipn pars args| = #|br.1| ->
  closedn #|br.1| br.2 ->
  closed (iota_red pars args br).
Proof.
  intros clargs hnth hskip clbr.
  rewrite /iota_red.
  eapply ECSubst.closed_substl => //.
  now rewrite forallb_rev forallb_skipn.
  now rewrite List.rev_length hskip Nat.add_0_r.
Qed.

Definition disable_prop_cases fl := {| with_prop_case := false; with_guarded_fix := fl.(@with_guarded_fix) |}.

Lemma isFix_mkApps t l : isFix (mkApps t l) = isFix t && match l with [] => true | _ => false end.
Proof.
  induction l using rev_ind; cbn.
  - now rewrite andb_true_r.
  - rewrite mkApps_app /=. now destruct l => /= //; rewrite andb_false_r.
Qed.

Lemma optimize_correct {efl : EEnvFlags} {fl} Σ t v :
  wf_glob Σ ->
  closed_env Σ ->
  @Ee.eval fl Σ t v ->
  closed t ->
  @Ee.eval (disable_prop_cases fl) (optimize_env Σ) (optimize Σ t) (optimize Σ v).
Proof.
  intros wfΣ clΣ ev.
  induction ev; simpl in *.

  - move/andP => [] cla clt. econstructor; eauto.
  - move/andP => [] clf cla.
    eapply eval_closed in ev2; tea.
    eapply eval_closed in ev1; tea.
    econstructor; eauto.
    rewrite optimize_csubst // in IHev3.
    apply IHev3. eapply closed_csubst => //.

  - move/andP => [] clb0 clb1. rewrite optimize_csubst in IHev2.
    now eapply eval_closed in ev1.
    econstructor; eauto. eapply IHev2, closed_csubst => //.
    now eapply eval_closed in ev1.

  - move/andP => [] cld clbrs. rewrite optimize_mkApps in IHev1.
    have := (eval_closed _ clΣ _ _ cld ev1); rewrite closedn_mkApps => /andP[] _ clargs.
    rewrite optimize_iota_red in IHev2.
    eapply eval_closed in ev1 => //.
    destruct EGlobalEnv.inductive_isprop_and_pars as [[]|]eqn:isp => //. noconf e.
    eapply Ee.eval_iota; eauto.
    now rewrite -is_propositional_optimize.
    rewrite nth_error_map e0 //. now len.
    eapply IHev2.
    eapply closed_iota_red => //; tea.
    eapply nth_error_forallb in clbrs; tea. cbn in clbrs.
    now rewrite Nat.add_0_r in clbrs.
  
  - move/andP => [] cld clbrs. rewrite e e0 /=.
    subst brs. cbn in clbrs. rewrite Nat.add_0_r andb_true_r in clbrs.
    rewrite optimize_substl in IHev2. 
    eapply All_forallb, All_repeat => //.
    rewrite map_optimize_repeat_box in IHev2.
    apply IHev2.
    eapply closed_substl.
    eapply All_forallb, All_repeat => //.
    now rewrite repeat_length Nat.add_0_r.

  - move/andP => [] clf cla. rewrite optimize_mkApps in IHev1.
    simpl in *.
    eapply eval_closed in ev1 => //.
    rewrite closedn_mkApps in ev1.
    move: ev1 => /andP [] clfix clargs.
    eapply Ee.eval_fix; eauto.
    rewrite map_length.
    eapply optimize_cunfold_fix; tea.
    eapply closed_fix_subst. tea.
    rewrite optimize_mkApps in IHev3. apply IHev3.
    rewrite closedn_mkApps clargs.
    eapply eval_closed in ev2; tas. rewrite ev2 /= !andb_true_r.
    eapply closed_cunfold_fix; tea.

  - move/andP => [] clf cla.
    eapply eval_closed in ev1 => //.
    rewrite closedn_mkApps in ev1.
    move: ev1 => /andP [] clfix clargs.
    eapply eval_closed in ev2; tas.
    rewrite optimize_mkApps in IHev1 |- *.
    simpl in *. eapply Ee.eval_fix_value. auto. auto. auto.
    eapply optimize_cunfold_fix; eauto.
    eapply closed_fix_subst => //.
    now rewrite map_length. 
  
  - move/andP => [] clf cla.
    eapply eval_closed in ev1 => //.
    eapply eval_closed in ev2; tas.
    simpl in *. eapply Ee.eval_fix'. auto. auto.
    eapply optimize_cunfold_fix; eauto.
    eapply closed_fix_subst => //.
    eapply IHev2; tea. eapply IHev3.
    apply/andP; split => //.
    eapply closed_cunfold_fix; tea.

  - move/andP => [] cd clbrs. specialize (IHev1 cd).
    rewrite closedn_mkApps in IHev2.
    move: (eval_closed _ clΣ _ _ cd ev1).
    rewrite closedn_mkApps.
    move/andP => [] clfix clargs.
    forward IHev2.
    { rewrite clargs clbrs !andb_true_r.
      eapply closed_cunfold_cofix; tea. }
    rewrite -> optimize_mkApps in IHev1, IHev2. simpl.
    destruct EGlobalEnv.inductive_isprop_and_pars as [[[] pars]|] eqn:isp => //.
    destruct brs as [|[a b] []]; simpl in *; auto.
    simpl in IHev1.
    eapply Ee.eval_cofix_case. tea.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    apply IHev2.
    eapply Ee.eval_cofix_case; tea.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    simpl in *.
    eapply Ee.eval_cofix_case; tea.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    eapply Ee.eval_cofix_case; tea.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    
  - intros cd. specialize (IHev1 cd).
    move: (eval_closed _ clΣ _ _ cd ev1).
    rewrite closedn_mkApps; move/andP => [] clfix clargs. forward IHev2.
    { rewrite closedn_mkApps clargs andb_true_r. eapply closed_cunfold_cofix; tea. }
    destruct EGlobalEnv.inductive_isprop_and_pars as [[[] pars]|] eqn:isp; auto.
    rewrite -> optimize_mkApps in IHev1, IHev2. simpl in *.
    econstructor; eauto.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    rewrite -> optimize_mkApps in IHev1, IHev2. simpl in *.
    econstructor; eauto.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
  
  - rewrite /declared_constant in isdecl.
    move: (lookup_env_optimize Σ c wfΣ); rewrite isdecl /= //.
    intros hl.
    econstructor; tea. cbn. rewrite e //.
    apply IHev.
    eapply lookup_env_closed in clΣ; tea.
    move: clΣ. rewrite /closed_decl e //.
  
  - move=> cld.
    eapply eval_closed in ev1; tea.
    move: ev1; rewrite closedn_mkApps /= => clargs.
    destruct EGlobalEnv.inductive_isprop_and_pars as [[[] pars']|] eqn:isp => //.
    rewrite optimize_mkApps in IHev1.
    rewrite optimize_nth in IHev2.
    specialize (IHev1 cld).
    eapply Ee.eval_proj; tea. noconf e.
    now rewrite -is_propositional_optimize.
    eapply IHev2.
    rewrite nth_nth_error.
    destruct nth_error eqn:hnth => //.
    eapply nth_error_forallb in hnth; tea.

  - now rewrite e.

  - move/andP => [] clf cla.
    specialize (IHev1 clf). specialize (IHev2 cla).
    eapply Ee.eval_app_cong; eauto.
    eapply Ee.eval_to_value in ev1.
    destruct ev1; simpl in *; eauto.
    * destruct t => //; rewrite optimize_mkApps /=.
    * destruct with_guarded_fix.
      + destruct t => /= //; rewrite optimize_mkApps /=;
        rewrite (negbTE (isLambda_mkApps _ _ _)) // (negbTE (isBox_mkApps _ _ _)) // /=; rewrite !isFixApp_mkApps //.
      + destruct t => /= //; rewrite optimize_mkApps /=;
        rewrite (negbTE (isLambda_mkApps _ _ _)) // (negbTE (isBox_mkApps _ _ _)) // /=; rewrite !isFix_mkApps //.
    * destruct f0 => //.
      rewrite optimize_mkApps /=.
      unfold Ee.isFixApp in i.
      rewrite decompose_app_mkApps /= in i => //.
      destruct with_guarded_fix; try rewrite orb_true_r /= // in i.
      discriminate.
  - destruct t => //.
    all:constructor; eauto.
Qed.
(* 
Lemma optimize_extends Σ Σ' : 
  wf_glob Σ' ->
  extends Σ Σ' ->
  forall t b, optimize Σ t = b -> optimize Σ' t = b.
Proof.
  intros wf ext.
  induction t using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [f_equal; solve_all].
  destruct inductive_isp
  rewrite (extends_is_propositional wf ext).
 *)

From MetaCoq.Erasure Require Import EEtaExpanded.

Lemma isLambda_optimize Σ t : isLambda t -> isLambda (optimize Σ t).
Proof. destruct t => //. Qed.
Lemma isBox_optimize Σ t : isBox t -> isBox (optimize Σ t).
Proof. destruct t => //. Qed.

Lemma optimize_expanded Σ t : expanded Σ t -> expanded Σ (optimize Σ t).
Proof.
  induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  all:rewrite ?optimize_mkApps.
  - eapply expanded_mkApps_expanded => //. solve_all.
  - cbn.
    destruct inductive_isprop_and_pars as [[[|] _]|] => /= //.
    2-3:constructor; eauto; solve_all.
    destruct branches eqn:heq.
    constructor; eauto; solve_all. cbn.
    destruct l => /=.
    eapply isEtaExp_expanded.
    eapply isEtaExp_substl. eapply forallb_repeat => //.
    destruct branches as [|[]]; cbn in heq; noconf heq.
    cbn -[isEtaExp] in *. depelim H1. cbn in H1.
    now eapply expanded_isEtaExp.
    constructor; eauto; solve_all.
    depelim H1. depelim H1. do 2 (constructor; intuition auto).
    solve_all.
  - cbn.
    destruct inductive_isprop_and_pars as [[[|] _]|] => /= //.
    constructor. all:constructor; auto.
  - cbn. eapply expanded_tFix. solve_all.
    rewrite isLambda_optimize //. now left.
    rewrite isBox_optimize //. now right.
  - eapply expanded_tConstruct_app; tea.
    now len. solve_all.
Qed.

Lemma optimize_expanded_irrel {efl : EEnvFlags} Σ t : wf_glob Σ -> expanded Σ t -> expanded (optimize_env Σ) t.
Proof.
  intros wf; induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  eapply expanded_tConstruct_app.
  destruct H as [[H ?] ?].
  split => //. split => //. red.
  red in H. rewrite lookup_env_optimize // /= H //. 1-2:eauto. auto. solve_all. 
Qed.

Lemma optimize_expanded_decl Σ t : expanded_decl Σ t -> expanded_decl Σ (optimize_decl Σ t).
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply optimize_expanded.
Qed.

Lemma optimize_expanded_decl_irrel {efl : EEnvFlags} Σ t : wf_glob Σ -> expanded_decl Σ t -> expanded_decl (optimize_env Σ) t.
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply optimize_expanded_irrel.
Qed.

Lemma optimize_env_expanded {efl : EEnvFlags} Σ :
  wf_glob Σ -> expanded_global_env Σ -> expanded_global_env (optimize_env Σ).
Proof.
  unfold expanded_global_env.
  intros wf. induction 1; cbn; constructor; auto.
  now depelim wf. cbn. 
  eapply optimize_expanded_decl in H0.
  depelim wf; now eapply optimize_expanded_decl_irrel.
Qed.

Lemma optimize_wellformed {efl : EEnvFlags} Σ n t :
  has_tBox -> has_tRel ->
  wf_glob Σ -> EWellformed.wellformed Σ n t -> EWellformed.wellformed Σ n (optimize Σ t).
Proof.
  intros wfΣ hbox hrel.
  induction t in n |- * using EInduction.term_forall_list_ind => //.
  all:try solve [cbn; rtoProp; intuition auto; solve_all].
  - cbn -[lookup_inductive]. move/and3P => [] hasc /andP[]hs ht hbrs.
    destruct EGlobalEnv.inductive_isprop_and_pars as [[[|] _]|] => /= //.
    destruct l as [|[br n'] [|l']] eqn:eql; simpl.
    all:rewrite ?hasc ?hs /= ?andb_true_r.
    rewrite IHt //.
    depelim X. cbn in hbrs.
    rewrite andb_true_r in hbrs.
    specialize (i _ hbrs).
    eapply wellformed_substl => //. solve_all. eapply All_repeat => //.
    now rewrite repeat_length.
    cbn in hbrs; rtoProp; solve_all. depelim X; depelim X. solve_all.
    do 2 depelim X. solve_all.
    do 2 depelim X. solve_all.
    rtoProp; solve_all. solve_all.
    rtoProp; solve_all. solve_all.
  - cbn -[lookup_inductive]. move/andP => [] /andP[]hasc hs ht.
    destruct EGlobalEnv.inductive_isprop_and_pars as [[[|] _]|] => /= //.
    all:rewrite hasc hs /=; eauto.
  - cbn. rtoProp; intuition auto; solve_all.
    unfold test_def in *. len. eauto.
  - cbn. rtoProp; intuition auto; solve_all.
    unfold test_def in *. len. eauto.
Qed.

Import EWellformed.

Lemma optimize_wellformed_irrel {efl : EEnvFlags} Σ t :
  wf_glob Σ ->
  forall n, wellformed Σ n t -> wellformed (optimize_env Σ) n t.
Proof.
  intros wfΣ. induction t using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [intros; rtoProp; intuition eauto; solve_all].
  - rewrite lookup_env_optimize //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct (cst_body c) => //.
  - rewrite lookup_env_optimize //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. 
  - rewrite lookup_env_optimize //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => /= //.
    intros; rtoProp; intuition auto; solve_all.
  - rewrite lookup_env_optimize //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //.
    rewrite andb_false_r => //.
    destruct nth_error => /= //.
    all:intros; rtoProp; intuition auto; solve_all.
Qed.


Lemma optimize_wellformed_decl_irrel {efl : EEnvFlags} Σ d :
  wf_glob Σ ->
  wf_global_decl Σ d -> wf_global_decl (optimize_env Σ) d.
Proof.
  intros wf; destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply optimize_wellformed_irrel.
Qed.

Lemma optimize_decl_wf {efl : EEnvFlags} Σ :
  has_tBox -> has_tRel -> wf_glob Σ -> 
  forall d, wf_global_decl Σ d -> wf_global_decl (optimize_env Σ) (optimize_decl Σ d).
Proof.
  intros hasb hasr wf d.
  intros hd.
  eapply optimize_wellformed_decl_irrel; tea.
  move: hd.
  destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply optimize_wellformed => //.
Qed.

Lemma fresh_global_optimize_env Σ kn : 
  fresh_global kn Σ ->
  fresh_global kn (optimize_env Σ).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma optimize_env_wf {efl : EEnvFlags} Σ :
  has_tBox -> has_tRel -> 
  wf_glob Σ -> wf_glob (optimize_env Σ).
Proof.
  intros hasb hasrel.
  induction 1; cbn; constructor; auto.
  - cbn. eapply optimize_decl_wf => //.
  - cbn. now eapply fresh_global_optimize_env.
Qed.

Definition optimize_program (p : eprogram) :=
  (EOptimizePropDiscr.optimize_env p.1, EOptimizePropDiscr.optimize p.1 p.2).

Definition optimize_program_wf {efl} (p : eprogram) {hastbox : has_tBox} {hastrel : has_tRel} :
  wf_eprogram efl p -> wf_eprogram efl (optimize_program p).
Proof.
  intros []; split.
  now eapply optimize_env_wf.
  cbn. eapply optimize_wellformed_irrel => //. now eapply optimize_wellformed.
Qed.

Definition optimize_program_expanded {efl} (p : eprogram) :
  wf_eprogram efl p ->
  expanded_eprogram_cstrs p -> expanded_eprogram_cstrs (optimize_program p).
Proof.
  unfold expanded_eprogram.
  move=> [wfe wft] /andP[] etae etat.
  apply/andP; split.
  cbn. eapply expanded_global_env_isEtaExp_env, optimize_env_expanded => //.
  now eapply isEtaExp_env_expanded_global_env.
  eapply expanded_isEtaExp.
  eapply optimize_expanded_irrel => //.
  now apply optimize_expanded, isEtaExp_expanded.
Qed.
