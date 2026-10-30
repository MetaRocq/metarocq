(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames Primitive BasicAst EnvMap.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction EArities
    ELiftSubst ESpineView EGlobalEnv EWellformed EEnvMap
    EWcbvEval EEtaExpanded ECSubst EWcbvEvalEtaInd EProgram.

Local Open Scope string_scope.
Set Asymmetric Patterns.
#[warning="-unknown-option"] Set Asymmetric Patterns No Implicits.
Import MonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Stdlib Require Import ssreflect ssrbool.

(** We assume [Prop </= Type] and universes are checked correctly in the following. *)
Local Existing Instance extraction_checker_flags.

Ltac introdep := let H := fresh in intros H; depelim H.

#[global]
Hint Constructors eval : core.

Import MRList (map_InP, map_InP_spec).

Section strip.
  Context (Σ : GlobalContextMap.t).

  Section Def.
  Import TermSpineView.
  Equations? strip (t : term) : term
    by wf t (fun x y : EAst.term => size x < size y) :=
  | e with TermSpineView.view e := {
    | tRel i => EAst.tRel i
    | tEvar ev args => EAst.tEvar ev (map_InP args (fun x H => strip x))
    | tLambda na M => EAst.tLambda na (strip M)
    | tApp u v napp nnil with construct_viewc u := {
      | view_construct kn c block_args with GlobalContextMap.lookup_inductive_pars Σ (inductive_mind kn) := {
        | Some npars :=
            mkApps (EAst.tConstruct kn c block_args) (List.skipn npars (map_InP v (fun x H => strip x)))
        | None => mkApps (EAst.tConstruct kn c block_args) (map_InP v (fun x H => strip x)) }
      | view_other u nconstr =>
        mkApps (strip u) (map_InP v (fun x H => strip x))
    }
    | tLetIn na b b' => EAst.tLetIn na (strip b) (strip b')
    | tCase ind c brs =>
      let brs' := map_InP brs (fun x H => (x.1, strip x.2)) in
      EAst.tCase (ind.1, 0) (strip c) brs'
    | tProj p c => EAst.tProj {| proj_ind := p.(proj_ind); proj_npars := 0; proj_arg := p.(proj_arg) |} (strip c)
    | tFix mfix idx =>
      let mfix' := map_InP mfix (fun d H => {| dname := dname d; dbody := strip d.(dbody); rarg := d.(rarg) |}) in
      EAst.tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := map_InP mfix (fun d H => {| dname := dname d; dbody := strip d.(dbody); rarg := d.(rarg) |}) in
      EAst.tCoFix mfix' idx
    | tBox => EAst.tBox
    | tVar n => EAst.tVar n
    | tConst n => EAst.tConst n
    | tConstruct ind i block_args => EAst.tConstruct ind i block_args
    | tPrim p => EAst.tPrim (map_primIn p (fun x H => strip x))
    | tLazy t => EAst.tLazy (strip t)
    | tForce t => EAst.tForce (strip t) }.
  Proof.
    all:try lia.
    all:try apply (In_size); tea.
    - eapply (In_size id size) in H. unfold id in H.
      change (fun x => size x) with size in *. lia.
    - rw size_mkApps.
      eapply (In_size id size) in H. change (fun x => size (id x)) with size in H. unfold id in H.  cbn. lia.
    - rw size_mkApps.
      eapply (In_size id size) in H. change (fun x => size (id x)) with size in H. unfold id in H.  cbn. lia.
    - now eapply size_mkApps_f.
    - pose proof (size_mkApps_l napp nnil).
      eapply (In_size id size) in H. change (fun x => size (id x)) with size in H. unfold id in H. lia.
    - eapply (In_size snd size) in H. cbn in H; lia.
    - eapply (In_size dbody size) in H; cbn in H; lia.
    - eapply (In_size dbody size) in H; cbn in H; lia.
    - destruct p as [? []]; cbn in H; eauto.
      intuition auto; subst; cbn; try lia.
      eapply (In_size id size) in H0. unfold id in H0.
      change (fun x => size x) with size in H0. lia.
  Qed.
  End Def.

  #[universes(polymorphic)] Hint Rewrite @map_primIn_spec @map_InP_spec : strip.

  Lemma map_repeat {A B} (f : A -> B) x n : map f (repeat x n) = repeat (f x) n.
  Proof using Type.
    now induction n; simpl; auto; rw IHn.
  Qed.

  Lemma map_strip_repeat_box n : map strip (repeat tBox n) = repeat tBox n.
  Proof using Type. now rw map_repeat. Qed.

  Arguments eqb : simpl never.

  Opaque strip_unfold_clause_1.
  Opaque strip.
  Opaque isEtaExp.
  Opaque isEtaExp_unfold_clause_1.

  Lemma closedn_mkApps k f l : closedn k (mkApps f l) = closedn k f && forallb (closedn k) l.
  Proof using Type.
    induction l in f |- *; cbn; auto.
    - now rw andb_true_r.
    - now rw IHl /= andb_assoc.
  Qed.

  Lemma closed_strip t k : closedn k t -> closedn k (strip t).
  Proof using Type.
    funelim (strip t); simp strip; rw -?strip_equation_1; toAll; simpl;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold test_def in *;
    simpl closed in *;
    try solve [simpl; subst; simpl closed; f_equal; auto; rtoProp; solve_all; solve_all]; try easy.
    - solve_all_k 6.
    - rw !closedn_mkApps in H1 *.
      rtoProp; intuition auto.
      solve_all.
    - rw !closedn_mkApps /= in H0 *. rtoProp.
      rw forallb_skipn; solve_all. solve_all.
    - rw !closedn_mkApps /= in H0 *. rtoProp. repeat solve_all.
  Qed.

  Hint Rewrite @forallb_InP_spec : isEtaExp.
  Transparent isEtaExp_unfold_clause_1.

  Local Lemma strip_mkApps_nonnil f v :
    ~~ isApp f -> v <> [] ->
    strip (mkApps f v) = match construct_viewc f with
      | view_construct kn c block_args =>
        match lookup_inductive_pars Σ (inductive_mind kn) with
        | Some npars => mkApps (EAst.tConstruct kn c block_args) (List.skipn npars (map strip v))
        | None => mkApps (EAst.tConstruct kn c block_args) (map strip v)
        end
      | view_other u nconstr => mkApps (strip f) (map strip v)
    end.
  Proof using Type.
    intros napp hv. rw strip_equation_1.
    destruct (TermSpineView.view_mkApps (TermSpineView.view (mkApps f v)) napp hv) as [hna [hv' ->]].
    simp strip; rw -strip_equation_1.
    destruct (construct_viewc f).
    2:cbn; simp strip => //.
    simp strip.
    rw GlobalContextMap.lookup_inductive_pars_spec.
    destruct lookup_inductive_pars as [pars|] eqn:epars; cbn; simp strip => //.
  Qed.

  Lemma strip_mkApps f v : ~~ isApp f ->
    strip (mkApps f v) = match construct_viewc f with
      | view_construct kn c block_args =>
        match lookup_inductive_pars Σ (inductive_mind kn) with
        | Some npars => mkApps (EAst.tConstruct kn c block_args) (List.skipn npars (map strip v))
        | None => mkApps (EAst.tConstruct kn c block_args) (map strip v)
        end
      | view_other u nconstr => mkApps (strip f) (map strip v)
    end.
  Proof using Type.
    intros napp.
    destruct v using rev_case; simpl.
    - destruct construct_viewc => //. simp strip.
      destruct lookup_inductive_pars as [|] => //.
      now rw skipn_nil //.
    - apply (strip_mkApps_nonnil f (v ++ [x])) => //.
  Qed.

  Lemma lookup_inductive_pars_constructor_pars_args {ind n pars args} :
    lookup_constructor_pars_args Σ ind n = Some (pars, args) ->
    lookup_inductive_pars Σ (inductive_mind ind) = Some pars.
  Proof using Type.
    rw /lookup_constructor_pars_args /lookup_inductive_pars.
    rw /lookup_constructor /lookup_inductive. destruct lookup_minductive => //.
    cbn. do 2 destruct nth_error => //. congruence.
  Qed.

  Lemma strip_csubst a k b :
    closed a ->
    isEtaExp Σ a ->
    isEtaExp Σ b ->
    strip (ECSubst.csubst a k b) = ECSubst.csubst (strip a) k (strip b).
  Proof using Type.
    intros cla etaa; move cla before a. move etaa before a.
    funelim (strip b); cbn; simp strip isEtaExp; rw -?isEtaExp_equation_1 -?strip_equation_1; toAll; simpl;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.

    - destruct Nat.compare => //.
    - f_equal. rtoProp. solve_all. destruct block_args; inv H0. eauto.
    - f_equal. solve_all.  move/andP: b => [] _ he. solve_all.
    - specialize (H a etaa cla k).
      rw !csubst_mkApps in H1 *.
      rw isEtaExp_mkApps_napp // in H1.
      destruct construct_viewc.
      * cbn. rw strip_mkApps //.
      * move/andP: H1 => [] et ev.
        rw -H //.
        assert (map (csubst a k) v <> []).
        { destruct v; cbn; congruence. }
        pose proof (etaExp_csubst Σ _ k _ etaa et).
        destruct (isApp (csubst a k t)) eqn:eqa.
        { destruct (decompose_app (csubst a k t)) eqn:eqk.
          rw (decompose_app_inv eqk) in H2 *.
          pose proof (decompose_app_notApp _ _ _ eqk).
          assert (l <> []).
          { intros ->. rw (decompose_app_inv eqk) in eqa. now rw eqa in H3. }
          rw isEtaExp_mkApps_napp // in H2.
          assert ((l ++ map (csubst a k) v)%list <> []).
          { destruct l; cbn; congruence. }

          destruct (construct_viewc t0) eqn:hc.
          { rw -mkApps_app /=.
            rw strip_mkApps //. rw strip_mkApps //.
            cbn -[lookup_inductive_pars].
            move/andP: H2 => [] ise hl.
            unfold isEtaExp_app in ise.
            destruct lookup_constructor_pars_args as [[pars args]|] eqn:eqpars => //.
            rw (lookup_inductive_pars_constructor_pars_args eqpars).
            rw -mkApps_app /= !skipn_map. f_equal.
            rw skipn_app map_app. f_equal.
            assert (pars - #|l| = 0). rtoProp. rename H2 into ise. eapply Nat.leb_le in ise; lia.
            rw H2 skipn_0.
            rw !map_map_compose.
            clear -etaa cla ev H0. solve_all. }
          { rw -mkApps_app.
            rw strip_mkApps //. rw hc.
            rw strip_mkApps // hc -mkApps_app map_app //.
            f_equal. f_equal.
            rw !map_map_compose.
            clear -etaa cla ev H0. solve_all. } }
        { rw strip_mkApps ?eqa //.
          destruct (construct_viewc (csubst a k t)) eqn:eqc.
          2:{ f_equal. rw !map_map_compose. clear -etaa cla ev H0. solve_all. }
          simp isEtaExp in H2.
          rw /isEtaExp_app in H2.
          destruct lookup_constructor_pars_args as [[pars args]|] eqn:eqpars => // /=.
          rw (lookup_inductive_pars_constructor_pars_args eqpars).
          assert (pars = 0). rtoProp. eapply Nat.leb_le in H2. lia.
          subst pars. rw skipn_0.
          simp strip; rw -strip_equation_1.
          { f_equal. rw !map_map_compose. clear -etaa cla ev H0. solve_all. } }
    - pose proof (etaExp_csubst _ _ k _ etaa H0).
      rw !csubst_mkApps /= in H1 *.
      assert (map (csubst a k) v <> []).
      { destruct v; cbn; congruence. }
      rw strip_mkApps //.
      rw isEtaExp_Constructor // in H1.
      move/andP: H1. rw length_map. move=> [] etaapp etav.
      cbn -[lookup_inductive_pars].
      unfold isEtaExp_app in etaapp.
      rw GlobalContextMap.lookup_inductive_pars_spec in Heq.
      rw Heq in etaapp *.
      f_equal.
      now destruct block_args; inv etav.
      rw map_skipn. f_equal.
      rw !map_map_compose.
      rw isEtaExp_Constructor // in H0. rtoProp. solve_all.
    - pose proof (etaExp_csubst _ _ k _ etaa H0).
      rw !csubst_mkApps /= in H1 *.
      assert (map (csubst a k) v <> []).
      { destruct v; cbn; congruence. }
      rw strip_mkApps //.
      rw isEtaExp_Constructor // in H1.
      rw GlobalContextMap.lookup_inductive_pars_spec in Heq.
      move/andP: H1. rw length_map. move=> [] etaapp etav.
      cbn -[lookup_inductive_pars].
      unfold isEtaExp_app in etaapp.
      destruct lookup_constructor_pars_args as [[pars args]|] eqn:eqpars => //.
      now rw (lookup_inductive_pars_constructor_pars_args eqpars) in Heq.
  Qed.

  Lemma strip_substl s t :
    forallb (closedn 0) s ->
    forallb (isEtaExp Σ) s ->
    isEtaExp Σ t ->
    strip (substl s t) = substl (map strip s) (strip t).
  Proof using Type.
    induction s in t |- *; simpl; auto.
    move=> /andP[] cla cls /andP[] etaa etas etat.
    rw IHs //. now eapply etaExp_csubst. f_equal.
    now rw strip_csubst.
  Qed.

  Lemma strip_iota_red pars args br :
    forallb (closedn 0) args ->
    forallb (isEtaExp Σ) args ->
    isEtaExp Σ br.2 ->
    strip (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map strip args) (on_snd strip br).
  Proof using Type.
    intros cl etaargs etabr.
    unfold EGlobalEnv.iota_red.
    rw strip_substl //.
    rw forallb_rev forallb_skipn //.
    rw forallb_rev forallb_skipn //.
    now rw map_rev map_skipn.
  Qed.

  Lemma strip_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def strip) mfix) = map strip (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst.
    rw length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto. now simp strip.
  Qed.

  Lemma strip_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def strip) mfix) = map strip (EGlobalEnv.cofix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.cofix_subst.
    rw length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto. now simp strip.
  Qed.

  Lemma strip_cunfold_fix mfix idx n f :
    forallb (closedn 0) (fix_subst mfix) ->
    forallb (fun d =>  isLambda (dbody d) && isEtaExp Σ (dbody d)) mfix ->
    cunfold_fix mfix idx = Some (n, f) ->
    cunfold_fix (map (map_def strip) mfix) idx = Some (n, strip f).
  Proof using Type.
    intros hfix heta.
    unfold cunfold_fix.
    rw nth_error_map.
    destruct nth_error eqn:heq.
    intros [= <- <-] => /=. f_equal. f_equal.
    rw strip_substl //.
    now apply isEtaExp_fix_subst.
    solve_all. eapply nth_error_all in heta; tea. cbn in heta.
    rtoProp; intuition auto.
    f_equal. f_equal. apply strip_fix_subst.
    discriminate.
  Qed.


  Lemma strip_cunfold_cofix mfix idx n f :
    forallb (closedn 0) (cofix_subst mfix) ->
    forallb (isEtaExp Σ ∘ dbody) mfix ->
    cunfold_cofix mfix idx = Some (n, f) ->
    cunfold_cofix (map (map_def strip) mfix) idx = Some (n, strip f).
  Proof using Type.
    intros hcofix heta.
    unfold cunfold_cofix.
    rw nth_error_map.
    destruct nth_error eqn:heq.
    intros [= <- <-] => /=. f_equal.
    rw strip_substl //.
    now apply isEtaExp_cofix_subst.
    solve_all. now eapply nth_error_all in heta; tea.
    f_equal. f_equal. apply strip_cofix_subst.
    discriminate.
  Qed.

  Lemma strip_nth {n l d} :
    strip (nth n l d) = nth n (map strip l) (strip d).
  Proof using Type.
    induction l in n |- *; destruct n; simpl; auto.
  Qed.

End strip.

#[universes(polymorphic)] Global Hint Rewrite @map_primIn_spec @map_InP_spec : strip.
Tactic Notation "simp_eta" "in" hyp(H) := simp isEtaExp in H; rw -?isEtaExp_equation_1 in H.
Ltac simp_eta := simp isEtaExp; rw -?isEtaExp_equation_1.
Tactic Notation "simp_strip" "in" hyp(H) := simp strip in H; rw -?strip_equation_1 in H.
Ltac simp_strip := simp strip; rw -?strip_equation_1.

Definition strip_constant_decl Σ cb :=
  {| cst_body := option_map (strip Σ) cb.(cst_body) |}.

Definition strip_inductive_decl idecl :=
  {| ind_finite := idecl.(ind_finite); ind_npars := 0; ind_bodies := idecl.(ind_bodies) |}.

Definition strip_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (strip_constant_decl Σ cb)
  | InductiveDecl idecl => InductiveDecl (strip_inductive_decl idecl)
  end.

Definition strip_env Σ :=
  map (on_snd (strip_decl Σ)) Σ.(GlobalContextMap.global_decls).

Definition strip_program (p : eprogram_env) : eprogram :=
  (ERemoveParams.strip_env p.1, ERemoveParams.strip p.1 p.2).

Import EGlobalEnv.

Lemma lookup_env_strip Σ kn :
  lookup_env (strip_env Σ) kn =
  option_map (strip_decl Σ) (lookup_env Σ.(GlobalContextMap.global_decls) kn).
Proof.
  unfold strip_env.
  destruct Σ as [Σ map repr wf]; cbn.
  induction Σ at 2 4; simpl; auto.
  case: eqb_spec => //.
Qed.

Lemma lookup_constructor_strip {Σ kn c} :
  lookup_constructor (strip_env Σ) kn c =
  match lookup_constructor Σ.(GlobalContextMap.global_decls) kn c with
  | Some (mdecl, idecl, cdecl) => Some (strip_inductive_decl mdecl, idecl, cdecl)
  | None => None
  end.
Proof.
  rw /lookup_constructor /lookup_inductive /lookup_minductive.
  rw lookup_env_strip.
  destruct lookup_env as [[]|] => /= //.
  do 2 destruct nth_error => //.
Qed.

Lemma lookup_constructor_pars_args_strip (Σ : GlobalContextMap.t) i n npars nargs :
  EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (npars, nargs) ->
  EGlobalEnv.lookup_constructor_pars_args (strip_env Σ) i n = Some (0, nargs).
Proof.
  rw /EGlobalEnv.lookup_constructor_pars_args. rw lookup_constructor_strip //=.
  destruct EGlobalEnv.lookup_constructor => //. destruct p as [[] ?] => //=. now intros [= <- <-].
Qed.

Lemma is_propositional_strip (Σ : GlobalContextMap.t) ind :
  match inductive_isprop_and_pars Σ.(GlobalContextMap.global_decls) ind with
  | Some (prop, npars) =>
    inductive_isprop_and_pars (strip_env Σ) ind = Some (prop, 0)
  | None =>
    inductive_isprop_and_pars (strip_env Σ) ind = None
  end.
Proof.
  rw /inductive_isprop_and_pars /lookup_inductive /lookup_minductive.
  rw lookup_env_strip.
  destruct lookup_env; simpl; auto.
  destruct g; simpl; auto. destruct nth_error => //.
Qed.

Lemma is_propositional_cstr_strip {Σ : GlobalContextMap.t} {ind c} :
  match constructor_isprop_pars_decl Σ.(GlobalContextMap.global_decls) ind c with
  | Some (prop, npars, cdecl) =>
    constructor_isprop_pars_decl (strip_env Σ) ind c = Some (prop, 0, cdecl)
  | None =>
  constructor_isprop_pars_decl (strip_env Σ) ind c = None
  end.
Proof.
  rw /constructor_isprop_pars_decl /lookup_constructor /lookup_inductive /lookup_minductive.
  rw lookup_env_strip.
  destruct lookup_env; simpl; auto.
  destruct g; simpl; auto. do 2 destruct nth_error => //.
Qed.

Lemma lookup_inductive_pars_strip {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind :
  wf_glob Σ ->
  forall pars, lookup_inductive_pars Σ ind = Some pars ->
  EGlobalEnv.lookup_inductive_pars (strip_env Σ) ind = Some 0.
Proof.
  rw /lookup_inductive_pars => wf pars.
  rw /lookup_inductive /lookup_minductive.
  rw (lookup_env_strip _ ind).
  destruct lookup_env as [[decl|]|] => //=.
Qed.

Arguments eval {wfl}.

Arguments isEtaExp : simpl never.

Lemma isEtaExp_mkApps {Σ} {f u} : isEtaExp Σ (tApp f u) ->
  let (hd, args) := decompose_app (tApp f u) in
  match construct_viewc hd with
  | view_construct kn c block_args =>
    args <> [] /\ f = mkApps hd (remove_last args) /\ u = last args u /\
    isEtaExp_app Σ kn c #|args| && forallb (isEtaExp Σ) args && is_nil block_args
  | view_other _ discr =>
    [&& isEtaExp Σ hd, forallb (isEtaExp Σ) args, isEtaExp Σ f & isEtaExp Σ u]
  end.
Proof.
  move/(isEtaExp_mkApps Σ f [u]).
  cbn -[decompose_app]. destruct decompose_app eqn:da.
  destruct construct_viewc eqn:cv => //.
  intros ->.
  pose proof (decompose_app_inv da).
  pose proof (decompose_app_notApp _ _ _ da).
  destruct l using rev_case. cbn. intuition auto. solve_discr. noconf H.
  rw mkApps_app in H. noconf H.
  rw remove_last_app last_last. intuition auto.
  destruct l; cbn in *; congruence.
  pose proof (decompose_app_inv da).
  pose proof (decompose_app_notApp _ _ _ da).
  destruct l using rev_case. cbn. intuition auto. destruct t => //.
  rw mkApps_app in H. noconf H.
  move=> /andP[] etat. rw forallb_app => /andP[] etal /=.
  rw andb_true_r => etaa. rw etaa andb_true_r.
  rw etat etal. cbn. rw andb_true_r.
  eapply isEtaExp_mkApps_intro; auto; solve_all.
Qed.

Lemma decompose_app_tApp_split f a hd args :
  decompose_app (tApp f a) = (hd, args) -> f = mkApps hd (remove_last args) /\ a = last args a.
Proof.
  unfold decompose_app. cbn.
  move/decompose_app_rec_inv' => [n [napp [hskip heq]]].
  rw -(firstn_skipn n args).
  rw -hskip. rw last_last; split => //.
  rw heq. f_equal.
  now rw remove_last_app.
Qed.

Arguments lookup_inductive_pars_constructor_pars_args {Σ ind n pars args}.

Lemma strip_tApp {Σ : GlobalContextMap.t} f a : isEtaExp Σ f -> isEtaExp Σ a -> strip Σ (EAst.tApp f a) = EAst.tApp (strip Σ f) (strip Σ a).
Proof.
  move=> etaf etaa.
  pose proof (isEtaExp_mkApps_intro _ _ [a] etaf).
  forward H by eauto.
  move/isEtaExp_mkApps: H.
  destruct decompose_app eqn:da.
  destruct construct_viewc eqn:cv => //.
  { intros [? [? []]]. rw H0 /=.
    rw -[EAst.tApp _ _ ](mkApps_app _ _ [a]).
    move/andP: H2 => []. rw /isEtaExp_app.
    rw !strip_mkApps // cv.
    destruct lookup_constructor_pars_args as [[pars args]|] eqn:hl => //.
    rw (lookup_inductive_pars_constructor_pars_args hl).
    intros hpars etal.
    rw -[EAst.tApp _ _ ](mkApps_app _ _ [strip Σ a]).
    f_equal. rw !skipn_map !skipn_app map_app. f_equal.
    assert (pars - #|remove_last l| = 0) as ->.
    2:{ rw skipn_0 //. }
    rw H0 in etaf.
    rw isEtaExp_mkApps_napp // in etaf.
    simp construct_viewc in etaf.
    move/andP: etaf => []. rw /isEtaExp_app hl.
    move => /andP[] /Nat.leb_le. lia. }
  { move/and4P=> [] iset isel _ _. rw (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    rw strip_mkApps //.
    destruct (decompose_app_tApp_split _ _ _ _ da).
    rw cv. rw H0.
    rw strip_mkApps // cv.
    rw -[EAst.tApp _ _ ](mkApps_app _ _ [strip Σ a]). f_equal.
    rw -[(_ ++ _)%list](map_app (strip Σ) _ [a]).
    f_equal.
    assert (l <> []).
    { destruct l; try congruence. eapply decompose_app_inv in da. cbn in *. now subst t. }
    rw H1.
    now apply remove_last_last. }
Qed.

Module Fast.
  Section faststrip.
    Context (Σ : GlobalContextMap.t).

    Equations strip (app : list term) (t : term) : term := {
    | app, tEvar ev args => mkApps (EAst.tEvar ev (strip_args args)) app
    | app, tLambda na M => mkApps (EAst.tLambda na (strip [] M)) app
    | app, tApp u v => strip (strip [] v :: app) u
    | app, tLetIn na b b' => mkApps (EAst.tLetIn na (strip [] b) (strip [] b')) app
    | app, tCase ind c brs =>
        let brs' := strip_brs brs in
        mkApps (EAst.tCase (ind.1, 0) (strip [] c) brs') app
    | app, tProj p c => mkApps (EAst.tProj {| proj_ind := p.(proj_ind); proj_npars := 0; proj_arg := p.(proj_arg) |} (strip [] c)) app
    | app, tFix mfix idx =>
        let mfix' := strip_defs mfix in
        mkApps (EAst.tFix mfix' idx) app
    | app, tCoFix mfix idx =>
        let mfix' := strip_defs mfix in
        mkApps (EAst.tCoFix mfix' idx) app
    | app, tConstruct kn c block_args with GlobalContextMap.lookup_inductive_pars Σ (inductive_mind kn) := {
        | Some npars => mkApps (EAst.tConstruct kn c block_args) (List.skipn npars app)
        | None => mkApps (EAst.tConstruct kn c block_args) app }
    | app, tPrim (primInt; primIntModel i) => mkApps (tPrim (primInt; primIntModel i)) app
    | app, tPrim (primFloat; primFloatModel f) => mkApps (tPrim (primFloat; primFloatModel f)) app
    | app, tPrim (primString; primStringModel f) => mkApps (tPrim (primString; primStringModel f)) app
    | app, tPrim (primArray; primArrayModel a) =>
      mkApps (tPrim (primArray; primArrayModel {| array_default := strip [] a.(array_default); array_value := strip_args a.(array_value) |})) app
    | app, tLazy t => mkApps (tLazy (strip [] t)) app
    | app, tForce t => mkApps (tForce (strip [] t)) app
    | app, x => mkApps x app }

    where strip_args (t : list term) : list term :=
    { | [] := []
      | a :: args := (strip [] a) :: strip_args args
    }

    where strip_brs (t : list (list BasicAst.name × term)) : list (list BasicAst.name × term) :=
    { | [] := []
      | a :: args := (a.1, (strip [] a.2)) :: strip_brs args }

    where strip_defs (t : mfixpoint term) : mfixpoint term :=
    { | [] := []
      | d :: defs := {| dname := dname d; dbody := strip [] d.(dbody); rarg := d.(rarg) |} :: strip_defs defs
    }.

    Local Ltac specIH :=
          match goal with
          | [ H : (forall args : list term, _) |- _ ] => specialize (H [] eq_refl)
          end.

    Lemma strip_acc_opt t :
      forall args, ERemoveParams.strip Σ (mkApps t args) = strip (map (ERemoveParams.strip Σ) args) t.
    Proof using Type.
      intros args.
      remember (map (ERemoveParams.strip Σ) args) as args'.
      revert args Heqargs'.
      set (P:= fun args' t fs => forall args, args' = map (ERemoveParams.strip Σ) args -> ERemoveParams.strip Σ (mkApps t args) = fs).
      apply (strip_elim P
        (fun l l' => map (ERemoveParams.strip Σ) l = l')
        (fun l l' => map (on_snd (ERemoveParams.strip Σ)) l = l')
        (fun l l' => map (map_def (ERemoveParams.strip Σ)) l = l')); subst P; cbn -[GlobalContextMap.lookup_inductive_pars isEtaExp ERemoveParams.strip]; clear.
      all: try reflexivity.
      all: intros *; simp_eta; simp_strip.
      all: try solve [intros; subst; rtoProp; rw strip_mkApps // /=; simp_strip; repeat specIH; repeat (f_equal; intuition eauto)].
      all: try solve [rw strip_mkApps //].
      - intros IHv IHu.
        specialize (IHv [] eq_refl). simpl in IHv.
        intros args ->. specialize (IHu (v :: args)).
        forward IHu. now rw -IHv. exact IHu.
      - intros Hl hargs args ->.
        rw strip_mkApps //=. simp_strip.
        f_equal. f_equal. cbn.
        do 2 f_equal. rw /map_array_model.
        specialize (Hl [] eq_refl). f_equal; eauto.
      - intros Hl args ->.
        rw strip_mkApps // /=.
        rw GlobalContextMap.lookup_inductive_pars_spec in Hl. now rw Hl.
      - intros Hl args ->.
        rw GlobalContextMap.lookup_inductive_pars_spec in Hl.
        now rw strip_mkApps // /= Hl.
      - intros IHa heq.
        specIH. now rw IHa.
      - intros IHa heq; specIH. f_equal; eauto. unfold on_snd. now rw IHa.
      - intros IHa heq; specIH. unfold map_def. f_equal; eauto. now rw IHa.
    Qed.

    Lemma strip_fast t : ERemoveParams.strip Σ t = strip [] t.
    Proof using Type. now apply (strip_acc_opt t []). Qed.

  End faststrip.

  Abbreviation strip' Σ := (strip Σ []).

  Definition strip_constant_decl Σ cb :=
    {| cst_body := option_map (strip' Σ) cb.(cst_body) |}.

  Definition strip_inductive_decl idecl :=
    {| ind_finite := idecl.(ind_finite); ind_npars := 0; ind_bodies := idecl.(ind_bodies) |}.

  Definition strip_decl Σ d :=
    match d with
    | ConstantDecl cb => ConstantDecl (strip_constant_decl Σ cb)
    | InductiveDecl idecl => InductiveDecl (strip_inductive_decl idecl)
    end.

  Definition strip_env Σ :=
    map (on_snd (strip_decl Σ)) Σ.(GlobalContextMap.global_decls).

  Lemma strip_env_fast Σ : ERemoveParams.strip_env Σ = strip_env Σ.
  Proof.
    unfold ERemoveParams.strip_env, strip_env.
    destruct Σ as [Σ map repr wf]. cbn.
    induction Σ at 2 4; cbn; auto.
    f_equal; eauto.
    destruct a as [kn []]; cbn; auto.
    destruct c as [[b|]]; cbn; auto. unfold on_snd; cbn.
    do 2 f_equal. unfold ERemoveParams.strip_constant_decl, strip_constant_decl.
    simpl. f_equal. f_equal. apply strip_fast.
  Qed.

End Fast.

Lemma isLambda_mkApps' f l :
  l <> nil ->
  ~~ EAst.isLambda (EAst.mkApps f l).
Proof.
  induction l using rev_ind; try congruence.
  rw mkApps_app /= //.
Qed.

Lemma isBox_mkApps' f l :
  l <> nil ->
  ~~ isBox (EAst.mkApps f l).
Proof.
  induction l using rev_ind; try congruence.
  rw mkApps_app /= //.
Qed.

Lemma isFix_mkApps' f l :
  l <> nil ->
  ~~ isFix (EAst.mkApps f l).
Proof.
  induction l using rev_ind; try congruence.
  rw mkApps_app /= //.
Qed.

Lemma isLambda_mkApps_Construct ind n block_args l :
  ~~ EAst.isLambda (EAst.mkApps (EAst.tConstruct ind n block_args) l).
Proof.
  induction l using rev_ind; cbn; try congruence.
  rw mkApps_app /= //.
Qed.

Lemma isBox_mkApps_Construct ind n block_args l :
  ~~ isBox (EAst.mkApps (EAst.tConstruct ind n block_args) l).
Proof.
  induction l using rev_ind; cbn; try congruence.
  rw mkApps_app /= //.
Qed.

Lemma isFix_mkApps_Construct ind n block_args l :
  ~~ isFix (EAst.mkApps (EAst.tConstruct ind n block_args) l).
Proof.
  induction l using rev_ind; cbn; try congruence.
  rw mkApps_app /= //.
Qed.

Lemma strip_isLambda Σ f :
  EAst.isLambda f = EAst.isLambda (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip]; (try simp_strip) => //.
  rw (negbTE (isLambda_mkApps' _ _ _)) //.
  rw (negbTE (isLambda_mkApps' _ _ _)) //; try apply map_nil => //.
  all:rw !(negbTE (isLambda_mkApps_Construct _ _ _ _)) //.
Qed.

Lemma strip_isBox Σ f :
  isBox f = isBox (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip] => //.
  all:rw map_InP_spec.
  rw (negbTE (isBox_mkApps' _ _ _)) //.
  rw (negbTE (isBox_mkApps' _ _ _)) //; try apply map_nil => //.
  all:rw !(negbTE (isBox_mkApps_Construct _ _ _ _)) //.
Qed.

Lemma isApp_mkApps u v : v <> nil -> isApp (mkApps u v).
Proof.
  destruct v using rev_case; try congruence.
  rw mkApps_app /= //.
Qed.

Lemma strip_isApp Σ f :
  ~~ EAst.isApp f ->
  ~~ EAst.isApp (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip] => //.
  all:rw map_InP_spec.
  all:rw isApp_mkApps //.
Qed.

Lemma strip_isFix Σ f :
  isFix f = isFix (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip] => //.
  all:rw map_InP_spec.
  rw (negbTE (isFix_mkApps' _ _ _)) //.
  rw (negbTE (isFix_mkApps' _ _ _)) //; try apply map_nil => //.
  all:rw !(negbTE (isFix_mkApps_Construct _ _ _ _)) //.
Qed.

Lemma strip_isFixApp Σ f :
  isFixApp f = isFixApp (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip] => //.
  all:rw map_InP_spec.
  all:rw isFixApp_mkApps isFixApp_mkApps //.
Qed.

Lemma strip_isConstructApp Σ f :
  isConstructApp f = isConstructApp (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip] => //.
  all:rw map_InP_spec.
  all:rw isConstructApp_mkApps isConstructApp_mkApps //.
Qed.

Lemma strip_isPrimApp Σ f :
  isPrimApp f = isPrimApp (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip] => //.
  all:rw map_InP_spec.
  all:rw !isPrimApp_mkApps //.
Qed.

Lemma strip_isLazyApp Σ f :
  isLazyApp f = isLazyApp (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip] => //.
  all:rw map_InP_spec.
  all:rw !isLazyApp_mkApps //.
Qed.

Lemma lookup_inductive_pars_is_prop_and_pars {Σ ind b pars} :
  inductive_isprop_and_pars Σ ind = Some (b, pars) ->
  lookup_inductive_pars Σ (inductive_mind ind) = Some pars.
Proof.
  rw /inductive_isprop_and_pars /lookup_inductive_pars /lookup_inductive /lookup_minductive.
  destruct lookup_env => //.
  destruct g => /= //.
  destruct nth_error => //. congruence.
Qed.

Lemma constructor_isprop_pars_decl_lookup {Σ ind c b pars decl} :
  constructor_isprop_pars_decl Σ ind c = Some (b, pars, decl) ->
  lookup_inductive_pars Σ (inductive_mind ind) = Some pars.
Proof.
  rw /constructor_isprop_pars_decl /lookup_constructor /lookup_inductive_pars /lookup_inductive /lookup_minductive.
  destruct lookup_env => //.
  destruct g => /= //.
  destruct nth_error => //. destruct nth_error => //. congruence.
Qed.

Lemma constructor_isprop_pars_inductive_pars {Σ ind c b pars decl} :
  constructor_isprop_pars_decl Σ ind c = Some (b, pars, decl) ->
  inductive_isprop_and_pars Σ ind = Some (b, pars).
Proof.
  rw /constructor_isprop_pars_decl /inductive_isprop_and_pars /lookup_constructor.
  destruct lookup_inductive as [[mdecl idecl]|] => /= //.
  destruct nth_error => //. congruence.
Qed.

Lemma lookup_constructor_lookup_inductive_pars {Σ ind c mdecl idecl cdecl} :
  lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
  lookup_inductive_pars Σ (inductive_mind ind) = Some mdecl.(ind_npars).
Proof.
  rw /lookup_constructor /lookup_inductive_pars /lookup_inductive /lookup_minductive.
  destruct lookup_env => //.
  destruct g => /= //.
  destruct nth_error => //. destruct nth_error => //. congruence.
Qed.

Lemma strip_mkApps_etaexp {Σ : GlobalContextMap.t} fn args :
  isEtaExp Σ fn ->
  strip Σ (EAst.mkApps fn args) = EAst.mkApps (strip Σ fn) (map (strip Σ) args).
Proof.
  destruct (decompose_app fn) eqn:da.
  rw (decompose_app_inv da).
  rw isEtaExp_mkApps_napp. now eapply decompose_app_notApp.
  destruct construct_viewc eqn:vc.
  + move=> /andP[] hl0 etal0.
    rw -mkApps_app.
    rw (strip_mkApps Σ (tConstruct ind n block_args)) // /=.
    rw strip_mkApps // /=.
    unfold isEtaExp_app in hl0.
    destruct lookup_constructor_pars_args as [[pars args']|] eqn:hl => //.
    rtoProp.
    eapply Nat.leb_le in H.
    rw (lookup_inductive_pars_constructor_pars_args hl).
    rw -mkApps_app. f_equal. rw map_app.
    rw skipn_app. len. assert (pars - #|l| = 0) by lia.
    now rw H1 skipn_0.
  + move=> /andP[] etat0 etal0.
    rw -mkApps_app !strip_mkApps; try now eapply decompose_app_notApp.
    rw vc. rw -mkApps_app !map_app //.
Qed.

 #[export] Instance Qpreserves_closedn (efl := all_env_flags) Σ : closed_env Σ ->
  Qpreserves (fun n x => closedn n x) Σ.
Proof.
  intros clΣ.
  split.
  - red. move=> n t.
    destruct t; cbn; intuition auto; try solve [constructor; auto].
    eapply on_evar; solve_all.
    eapply on_letin; rtoProp; intuition auto.
    eapply on_app; rtoProp; intuition auto.
    eapply on_case; rtoProp; intuition auto. solve_all.
    eapply on_fix. solve_all. solve_all.
    eapply on_cofix; solve_all.
    eapply on_prim; solve_all.
  - red. intros kn decl.
    move/(lookup_env_closed clΣ).
    unfold closed_decl. destruct EAst.cst_body => //.
  - red. move=> hasapp n t args. rw closedn_mkApps.
    split; intros; rtoProp; intuition auto; solve_all.
  - red. move=> hascase n ci discr brs. simpl.
    intros; rtoProp; intuition auto; solve_all.
  - red. move=> hasproj n p discr. simpl.
    intros; rtoProp; intuition auto; solve_all.
  - red. move=> t args clt cll.
    eapply closed_substl. solve_all. now rw Nat.add_0_r.
  - red. move=> n mfix idx. cbn.
    intros; rtoProp; intuition auto; solve_all.
  - red. move=> n mfix idx. cbn.
    intros; rtoProp; intuition auto; solve_all.
Qed.

Lemma strip_eval (efl := all_env_flags) {wfl:WcbvFlags} {wcon : with_constructor_as_block = false} {Σ : GlobalContextMap.t} t v :
  isEtaExp_env Σ ->
  closed_env Σ ->
  wf_glob Σ ->
  closedn 0 t ->
  isEtaExp Σ t ->
  eval Σ t v ->
  eval (strip_env Σ) (strip Σ t) (strip Σ v).
Proof.
  intros etaΣ clΣ wfΣ.
  revert t v.
  unshelve eapply (eval_preserve_mkApps_ind wfl wcon Σ (fun x y => eval (strip_env Σ) (strip Σ x) (strip Σ y))
    (fun n x => closedn n x) (Qpres := Qpreserves_closedn Σ clΣ)) => //.
  { intros. eapply eval_closed; tea. }
  all:intros; simpl in *.
  (* 1-15: try solve [econstructor; eauto]. *)
  all:repeat destruct_nary_times => //.
  - rw strip_tApp //.
    econstructor; eauto.

  - rw strip_tApp //. simp_strip in e1.
    econstructor; eauto.
    rw strip_csubst // in e. now simp_eta in i10.

  - simp_strip.
    rw strip_csubst // in e.
    econstructor; eauto.

  - simp_strip.
    set (brs' := map _ brs). cbn -[strip].
    cbn in H3.
    rw strip_mkApps // /= in e0.
    apply constructor_isprop_pars_decl_lookup in H2 as H1'.
    rw H1' in e0.
    pose proof (@is_propositional_cstr_strip Σ ind c).
    rw H2 in H1.
    econstructor; eauto.
    * rw nth_error_map H3 //.
    * len. cbn in H4, H5. rw length_skipn. lia.
    * cbn -[strip]. rw skipn_0. len.
    * cbn -[strip].
      have etaargs : forallb (isEtaExp Σ) args.
      { rw isEtaExp_Constructor in i6.
        now move/andP: i6 => [] /andP[]. }
      rw strip_iota_red // in e.
      rw closedn_mkApps in i4. now move/andP: i4.
      cbn. now eapply nth_error_forallb in H; tea.

  - subst brs. cbn in H4.
    rw andb_true_r in H4.
    rw strip_substl // in e.
    eapply All_forallb, All_repeat => //.
    eapply All_forallb, All_repeat => //.
    rw map_strip_repeat_box in e.
    simp_strip. set (brs' := map _ _).
    cbn -[strip]. eapply eval_iota_sing => //.
    now move: (is_propositional_strip Σ ind); rw H2.

  - rw strip_tApp //.
    rw strip_mkApps // /= in e1.
    simp_strip in e1.
    eapply eval_fix; tea.
    * rw length_map.
      eapply strip_cunfold_fix; tea.
      eapply closed_fix_subst. tea.
      move: i8; rw closedn_mkApps => /andP[] //.
      move: i10; rw isEtaExp_mkApps_napp // /= => /andP[] //. simp_eta.
    * move: e.
      rw -[tApp _ _](mkApps_app _ _ [av]).
      rw -[tApp _ _](mkApps_app _ _ [strip _ av]).
      rw strip_mkApps_etaexp // map_app //.

  - rw strip_tApp //.
    rw strip_tApp //.
    rw strip_mkApps //. simpl.
    simp_strip. set (mfix' := map _ _). simpl.
    rw strip_mkApps // /= in e0. simp_strip in e0.
    eapply eval_fix_value; tea.
    eapply strip_cunfold_fix; eauto.
    eapply closed_fix_subst => //.
    { move: i4.
      rw closedn_mkApps. now move/andP => []. }
    { move: i6. rw isEtaExp_mkApps_napp // /= => /andP[] //. now simp isEtaExp. }
    now rw length_map.

  - rw strip_tApp //. simp_strip in e0.
    simp_strip in e1.
    eapply eval_fix'; tea.
    eapply strip_cunfold_fix; tea.
    { eapply closed_fix_subst => //. }
    { simp isEtaExp in i10. }
    rw strip_tApp // in e.

  - simp_strip.
    rw strip_mkApps // /= in e0.
    simp_strip in e.
    simp_strip in e0.
    set (brs' := map _ _) in *; simpl.
    eapply eval_cofix_case; tea.
    eapply strip_cunfold_cofix; tea => //.
    { eapply closed_cofix_subst; tea.
      move: i5; rw closedn_mkApps => /andP[] //. }
    { move: i7. rw isEtaExp_mkApps_napp // /= => /andP[] //. now simp isEtaExp. }
    rw strip_mkApps_etaexp // in e.

  - destruct p as [[ind pars] arg].
    simp_strip.
    simp_strip in e.
    rw strip_mkApps // /= in e0.
    simp_strip in e0.
    rw strip_mkApps_etaexp // in e.
    simp_strip in e0.
    eapply eval_cofix_proj; tea.
    eapply strip_cunfold_cofix; tea.
    { eapply closed_cofix_subst; tea.
      move: i4; rw closedn_mkApps => /andP[] //. }
    { move: i6. rw isEtaExp_mkApps_napp // /= => /andP[] //. now simp isEtaExp. }

  - econstructor. red in H |- *.
    rw lookup_env_strip H //.
    now rw /strip_constant_decl H0.
    exact e.

  - simp_strip.
    rw strip_mkApps // /= in e0.
    rw (constructor_isprop_pars_decl_lookup H2) in e0.
    eapply eval_proj; eauto.
    move: (@is_propositional_cstr_strip Σ p.(proj_ind) 0). now rw H2. simpl.
    len. rw length_skipn. cbn in H3. lia.
    rw nth_error_skipn nth_error_map /= H4 //.

  - simp_strip. eapply eval_proj_prop => //.
    move: (is_propositional_strip Σ p.(proj_ind)); now rw H3.

  - rw !strip_tApp //.
    eapply eval_app_cong; tea.
    move: H1. eapply contraNN.
    rw -strip_isLambda -strip_isConstructApp -strip_isFixApp -strip_isBox -strip_isPrimApp
      -strip_isLazyApp // -strip_isFix //.

  - rw !strip_mkApps // /=.
    rw (lookup_constructor_lookup_inductive_pars H).
    eapply eval_mkApps_Construct; tea.
    + rw lookup_constructor_strip H //.
    + constructor. cbn [atom]. rw wcon lookup_constructor_strip H //.
    + rw /cstr_arity /=.
      move: H0; rw /cstr_arity /=.
      rw length_skipn length_map => ->. lia.
    + cbn in H0. eapply All2_skipn, All2_map.
      eapply All2_impl; tea; cbn -[strip].
      intros x y []; auto.

  - depelim X; simp strip; repeat constructor.
    eapply All2_over_undep in a. eapply All2_Set_All2 in ev. eapply All2_All2_Set. solve_all. now destruct b.
    now destruct a0.

  - simp_strip. simp_strip in e0. econstructor; tea.

  - destruct t => //.
    all:constructor; eauto. simp strip.
    cbn [atom strip] in H |- *.
    rw lookup_constructor_strip.
    destruct lookup_constructor eqn:hl => //. destruct p as [[] ?] => //.
Qed.

From MetaRocq.Erasure Require Import EEtaExpanded.

Lemma strip_declared_constructor {Σ : GlobalContextMap.t} {k mdecl idecl cdecl} :
  declared_constructor Σ.(GlobalContextMap.global_decls)  k mdecl idecl cdecl ->
  declared_constructor (strip_env Σ) k (strip_inductive_decl mdecl) idecl cdecl.
Proof.
  intros [[] ?]; do 2 split => //.
  red in H; red.
  rw lookup_env_strip H //.
Qed.

Lemma lookup_inductive_pars_spec {Σ} {mind} {mdecl} :
  declared_minductive Σ mind mdecl ->
  lookup_inductive_pars Σ mind = Some (ind_npars mdecl).
Proof.
  rw /declared_minductive /lookup_inductive_pars /lookup_minductive.
  now intros -> => /=.
Qed.

Definition switch_no_params (efl : EEnvFlags) :=
  {| has_axioms := has_axioms;
     has_cstr_params := false;
     term_switches := term_switches ;
     cstr_as_blocks := cstr_as_blocks
     |}.

(* Stripping preserves well-formedness directly, not caring about eta-expansion *)
Lemma strip_wellformed {efl} {Σ : GlobalContextMap.t} n t :
  cstr_as_blocks = false ->
  has_tApp ->
  @wf_glob efl Σ ->
  @wellformed efl Σ n t ->
  @wellformed (switch_no_params efl) (strip_env Σ) n (strip Σ t).
Proof.
  intros cab hasapp wfΣ.
  revert n.
  funelim (strip Σ t); try intros n.
  all:cbn -[strip lookup_constructor lookup_inductive]; simp_strip; intros.
  all:try solve[unfold wf_fix_gen in *; rtoProp; intuition auto; toAll; solve_all].
  - cbn -[strip]; simp_strip. intros; rtoProp; intuition auto.
    rw lookup_env_strip. destruct lookup_env eqn:hl => // /=.
    destruct g => /= //. destruct (cst_body c) => //.
  - rw cab in H |- *. cbn -[strip] in *.
    rw lookup_env_strip. destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => //. destruct nth_error => //.
  - cbn -[strip].
    rtoProp. move: H2. rw /wf_brs; cbn -[strip].
    rw lookup_env_strip. cbn in H1. destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => //. rtoProp; intuition auto. len.
    simp_strip. toAll; solve_all.
  - cbn -[strip] in H0 |- *.
    rw lookup_env_strip. destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g. cbn in H0. now rtoProp.
    destruct nth_error => //. all:rtoProp; intuition auto.
    destruct EAst.ind_ctors => //.
    destruct nth_error => //.
    all: eapply H; auto.
  - unfold wf_fix_gen in *. rw length_map. rtoProp; intuition auto. toAll; solve_all.
    now rw -strip_isLambda. toAll; solve_all.
  - primProp. rtoProp; intuition eauto; solve_all_k 6.
  - move:H1; rw !wellformed_mkApps //. rtoProp; intuition auto.
    all:toAll; solve_all.
  - move:H0; rw !wellformed_mkApps //. rtoProp; intuition auto.
    move: H1. cbn. rw cab.
    rw lookup_env_strip. destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => //. destruct nth_error => //.
    toAll; solve_all. eapply All_skipn. solve_all.
  - move:H0; rw !wellformed_mkApps //. rtoProp; intuition auto.
    move: H1. cbn. rw cab.
    rw lookup_env_strip. destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => //. destruct nth_error => //.
    toAll; solve_all.
Qed.

Lemma strip_wellformed_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t :
  cstr_as_blocks = false ->
  wf_glob Σ ->
  forall n, wellformed Σ n t -> wellformed (strip_env Σ) n t.
Proof.
  intros hcstrs wfΣ. induction t using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [intros; unfold wf_fix in *; rtoProp; intuition eauto; solve_all].
  - rw lookup_env_strip //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct (cst_body c) => //.
  - rw lookup_env_strip //.
    destruct lookup_env eqn:hl => // /=; intros; rtoProp; eauto.
    destruct g eqn:hg => /= //; intros; rtoProp; eauto.
    destruct cstr_as_blocks => //; repeat split; eauto.
    destruct nth_error => /= //.
    destruct nth_error => /= //.
  - rw /wf_brs; cbn; rw lookup_env_strip //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => /= //.
    intros; rtoProp; intuition auto; solve_all.
  - rw lookup_env_strip //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //.
    rw andb_false_r => //.
    destruct nth_error => /= //.
    destruct EAst.ind_ctors => /= //.
    all:intros; rtoProp; intuition auto; solve_all.
    destruct nth_error => //.
Qed.

Lemma strip_wellformed_decl_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} d :
  cstr_as_blocks = false ->
  wf_glob Σ ->
  wf_global_decl Σ d -> wf_global_decl (strip_env Σ) d.
Proof.
  intros hcstrs wf; destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply strip_wellformed_irrel.
Qed.

Lemma strip_decl_wf (efl := all_env_flags) {Σ : GlobalContextMap.t} :
  wf_glob Σ ->
  forall d, wf_global_decl Σ d ->
  wf_global_decl (efl := switch_no_params efl) (strip_env Σ) (strip_decl Σ d).
Proof.
  intros wf d.
  destruct d => /= //.
  destruct (cst_body c) => /= //.
  now apply (strip_wellformed (Σ := Σ) 0 t).
Qed.

Lemma fresh_global_strip_env {Σ : GlobalContextMap.t} kn :
  fresh_global kn Σ ->
  fresh_global kn (strip_env Σ).
Proof.
  unfold fresh_global. cbn. unfold strip_env.
  induction (GlobalContextMap.global_decls Σ); cbn; constructor; auto. cbn.
  now depelim H. depelim H. eauto.
Qed.

From MetaRocq.Erasure Require Import EProgram.

Program Fixpoint strip_env' Σ : EnvMap.fresh_globals Σ -> global_context :=
  match Σ with
  | [] => fun _ => []
  | hd :: tl => fun HΣ =>
    let Σg := GlobalContextMap.make tl (fresh_globals_cons_inv HΣ) in
    on_snd (strip_decl Σg) hd :: strip_env' tl (fresh_globals_cons_inv HΣ)
  end.

Lemma lookup_minductive_declared_minductive Σ ind mdecl :
  lookup_minductive Σ ind = Some mdecl <-> declared_minductive Σ ind mdecl.
Proof.
  unfold declared_minductive, lookup_minductive.
  destruct lookup_env => /= //. destruct g => /= //; split => //; congruence.
Qed.

Lemma lookup_minductive_declared_inductive Σ ind mdecl idecl :
  lookup_inductive Σ ind = Some (mdecl, idecl) <-> declared_inductive Σ ind mdecl idecl.
Proof.
  unfold declared_inductive, lookup_inductive.
  rewrite <- lookup_minductive_declared_minductive.
  destruct lookup_minductive => /= //.
  destruct nth_error eqn:hnth => //.
  split. intros [=]. subst. split => //.
  intros [[=] hnth']. subst. congruence.
  split => //. intros [[=] hnth']. congruence.
  split => //. intros [[=] hnth'].
Qed.

Lemma extends_lookup_inductive_pars {efl : EEnvFlags} {Σ Σ'} :
  extends Σ Σ' -> wf_glob Σ' ->
  forall ind t, lookup_inductive_pars Σ ind = Some t ->
    lookup_inductive_pars Σ' ind = Some t.
Proof.
  intros ext wf ind t.
  rw /lookup_inductive_pars.
  destruct (lookup_minductive Σ ind) eqn:hl => /= //.
  intros [= <-].
  apply lookup_minductive_declared_minductive in hl.
  eapply EExtends.weakening_env_declared_minductive in hl; tea.
  apply lookup_minductive_declared_minductive in hl. now rw hl.
Qed.

Lemma strip_extends {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  has_tApp ->
  extends Σ Σ' -> wf_glob Σ' ->
  forall n t, wellformed Σ n t -> strip Σ t = strip Σ' t.
Proof.
  intros hasapp hext hwf n t. revert n.
  funelim (strip Σ t); intros ?n; simp_strip  => /= //.
  all:try solve [intros; unfold wf_fix in *; rtoProp; intuition auto; f_equal; auto; toAll; solve_all].
  - intros; rtoProp; intuition auto.
    move: H1; rw wellformed_mkApps // => /andP[] wfu wfargs.
    rw strip_mkApps // Heq /=. f_equal; eauto. toAll; solve_all.
  - rw wellformed_mkApps // => /andP[] wfc wfv.
    rw strip_mkApps // /=.
    rw GlobalContextMap.lookup_inductive_pars_spec in Heq.
    eapply (extends_lookup_inductive_pars hext hwf) in Heq.
    rw Heq. f_equal. f_equal.
    toAll; solve_all.
  - rw wellformed_mkApps // => /andP[] wfc wfv.
    rw strip_mkApps // /=.
    move: Heq.
    rw GlobalContextMap.lookup_inductive_pars_spec.
    unfold wellformed in wfc. move/andP: wfc => [] /andP[] hacc hc bargs.
    unfold lookup_inductive_pars. destruct lookup_minductive eqn:heq => //.
    unfold lookup_constructor, lookup_inductive in hc. rw heq /= // in hc.
Qed.

Lemma strip_decl_extends {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  has_tApp ->
  extends Σ Σ' -> wf_glob Σ' ->
  forall d, wf_global_decl Σ d -> strip_decl Σ d = strip_decl Σ' d.
Proof.
  intros hast ext wf []; cbn.
  unfold strip_constant_decl.
  destruct (EAst.cst_body c) eqn:hc => /= //.
  intros hwf. f_equal. f_equal. f_equal.
  eapply strip_extends => //. exact hwf.
  intros _ => //.
Qed.

From MetaRocq.Erasure Require Import EGenericGlobalMap.

#[local]
Instance GT : GenTransform := { gen_transform := strip; gen_transform_inductive_decl := strip_inductive_decl }.
#[local]
Instance GTExt efl : has_tApp -> GenTransformExtends efl efl GT.
Proof.
  intros hasapp Σ t n wfΣ Σ' ext wf wf'.
  unfold gen_transform, GT.
  eapply strip_extends; tea.
Qed.
#[local]
Instance GTWf efl : GenTransformWf efl (switch_no_params efl) GT.
Proof.
  refine {| gen_transform_pre := fun _ _ => has_tApp /\ cstr_as_blocks = false |}; auto.
  - unfold wf_minductive; intros []. cbn. repeat rtoProp. intuition auto.
  - intros Σ n t [? ?] wfΣ wft. unfold gen_transform_env, gen_transform. simpl.
    eapply strip_wellformed => //.
Defined.

Lemma strip_extends' {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  has_tApp ->
  extends Σ Σ' ->
  wf_glob Σ ->
  wf_glob Σ' ->
  List.map (on_snd (strip_decl Σ)) Σ.(GlobalContextMap.global_decls) =
  List.map (on_snd (strip_decl Σ')) Σ.(GlobalContextMap.global_decls).
Proof.
  intros hast ext wf.
  now apply (gen_transform_env_extends' (gt := GTExt efl hast) ext).
Qed.

Lemma strip_extends_env {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  has_tApp ->
  extends Σ Σ' ->
  wf_glob Σ ->
  wf_glob Σ' ->
  extends (strip_env Σ) (strip_env Σ').
Proof.
  intros hast ext wf.
  now apply (gen_transform_extends (gt := GTExt efl hast) ext).
Qed.

Lemma strip_env_eq (efl := all_env_flags) (Σ : GlobalContextMap.t) : wf_glob Σ -> strip_env Σ = strip_env' Σ.(GlobalContextMap.global_decls) Σ.(GlobalContextMap.wf).
Proof.
  intros wf.
  unfold strip_env.
  destruct Σ; cbn. cbn in wf.
  induction global_decls in map, repr, wf0, wf |- * => //.
  cbn. f_equal.
  destruct a as [kn d]; unfold on_snd; cbn. f_equal. symmetry.
  eapply strip_decl_extends => //. cbn. cbn. eapply EExtends.extends_prefix_extends. now exists [(kn, d)]. auto. cbn. now depelim wf.
  set (Σg' := GlobalContextMap.make global_decls (fresh_globals_cons_inv wf0)).
  erewrite <- (IHglobal_decls (GlobalContextMap.map Σg') (GlobalContextMap.repr Σg')).
  2:now depelim wf.
  set (Σg := {| GlobalContextMap.global_decls := _ :: _ |}).
  symmetry. eapply (strip_extends' (Σ := Σg') (Σ' := Σg)) => //.
  cbn. eapply EExtends.extends_prefix_extends => //. now exists [a].
  cbn. now depelim wf.
Qed.

Lemma strip_env_wf (efl := all_env_flags) {Σ : GlobalContextMap.t} :
  wf_glob Σ -> wf_glob (efl := switch_no_params efl) (strip_env Σ).
Proof.
  intros wf.
  rw (strip_env_eq _ wf).
  destruct Σ as [Σ map repr fr]; cbn in *.
  induction Σ in map, repr, fr, wf |- *.
  - cbn. constructor.
  - cbn.
    set (Σg := GlobalContextMap.make Σ (fresh_globals_cons_inv fr)).
    constructor; eauto.
    eapply (IHΣ (GlobalContextMap.map Σg) (GlobalContextMap.repr Σg)). now depelim wf.
    depelim wf. cbn.
    rw -(strip_env_eq Σg). now cbn. cbn.
    now eapply (strip_decl_wf (Σ:=Σg)).
    rw -(strip_env_eq Σg). now depelim wf.
    eapply fresh_global_strip_env. now depelim fr.
Qed.

Lemma strip_program_wf (efl := all_env_flags) (p : eprogram_env) :
  wf_eprogram_env efl p ->
  wf_eprogram (switch_no_params efl) (strip_program p).
Proof.
  intros []; split => //.
  eapply (strip_env_wf H).
  now eapply strip_wellformed.
Qed.

Lemma strip_expanded {Σ : GlobalContextMap.t} {t} : expanded Σ t -> expanded (strip_env Σ) (strip Σ t).
Proof.
  induction 1 using expanded_ind.
  all:try solve[simp_strip; constructor; eauto; solve_all].
  - rw strip_mkApps_etaexp. now eapply expanded_isEtaExp.
    eapply expanded_mkApps_expanded => //. solve_all.
  - simp_strip; constructor; eauto. solve_all.
    rw -strip_isLambda //.
  - rw strip_mkApps // /=.
    rw (lookup_inductive_pars_spec (proj1 (proj1 H))).
    eapply expanded_tConstruct_app.
    eapply strip_declared_constructor; tea.
    len. rw length_skipn /= /EAst.cstr_arity /=.
    rw /EAst.cstr_arity in H0. lia.
    solve_all. eapply All_skipn. solve_all.
Qed.

Lemma strip_expanded_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded Σ t -> expanded (strip_env Σ) t.
Proof.
  intros wf; induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  eapply expanded_tConstruct_app.
  destruct H as [[H ?] ?].
  split => //. split => //. red.
  red in H. rw lookup_env_strip // /= H //. 1-2:eauto.
  cbn. rw /EAst.cstr_arity in H0. lia. solve_all.
Qed.

Lemma strip_expanded_decl {Σ : GlobalContextMap.t} t : expanded_decl Σ t -> expanded_decl (strip_env Σ) (strip_decl Σ t).
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply strip_expanded.
Qed.

Lemma strip_env_expanded (efl := all_env_flags) {Σ : GlobalContextMap.t} :
  wf_glob Σ -> expanded_global_env Σ -> expanded_global_env (strip_env Σ).
Proof.
  unfold expanded_global_env.
  intros wf. rw strip_env_eq //.
  destruct Σ as [Σ map repr wf']; cbn in *.
  intros exp; induction exp in map, repr, wf', wf |- *; cbn.
  - constructor; auto.
  - set (Σ' := GlobalContextMap.make Σ (fresh_globals_cons_inv wf')).
    constructor; auto.
    eapply IHexp. eapply Σ'. now depelim wf. cbn.
    eapply (strip_expanded_decl (Σ := Σ')) in H.
    rw -(strip_env_eq Σ'). cbn. now depelim wf.
    exact H.
Qed.

Import EProgram.

Lemma strip_program_expanded (efl := all_env_flags) (p : eprogram_env) :
  wf_eprogram_env efl p ->
  expanded_eprogram_env_cstrs p ->
  expanded_eprogram_cstrs (strip_program p).
Proof.
  unfold expanded_eprogram_env_cstrs, expanded_eprogram_cstrs.
  move=> [] wfe wft. move/andP => [] etaenv etap.
  apply/andP; split.
  eapply expanded_global_env_isEtaExp_env, strip_env_expanded => //.
  now eapply isEtaExp_env_expanded_global_env.
  now eapply expanded_isEtaExp, strip_expanded, isEtaExp_expanded.
Qed.
