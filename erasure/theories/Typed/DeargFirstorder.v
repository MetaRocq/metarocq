(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst Transform.
From MetaRocq.Erasure Require EEnvMap ERemoveParams.
From MetaRocq.Erasure Require Import EAst EInduction EPrimitive EGlobalEnv
  EFirstorder.
From MetaRocq.Erasure.Typed Require Import ExAst Optimize OptimizeCorrectness.

(** * Dearging keeps first-order values

  The masks computed by the dearging analysis ([analyze_env]) start, for the
  constructors of an inductive type, by removing the arguments whose erased
  type is a box or an arbitrary type, and the analysis then only marks more
  arguments as used. The constructors of first-order inductive types have
  first-order types as arguments: their masks remove nothing, and dearging
  changes first-order values only in their parameters. *)

(** ** The analysis only clears bits of constructor masks *)

Definition no_true (m : bitmask) := forallb negb m.

Definition mm_ok (mm : mib_masks) :=
  forallb (fun '(_, _, m) => no_true m) (ctor_masks mm).

Definition inds_ok (P : kername -> Prop) (inds : list (kername × mib_masks)) :=
  forall kn mm, In (kn, mm) inds -> P kn -> mm_ok mm.

Section AnalyzeOk.
  Context (P : kername -> Prop).

  Lemma get_mib_masks_In inds kn mm :
    get_mib_masks inds kn = Some mm -> In (kn, mm) inds.
  Proof.
    rewrite /get_mib_masks.
    destruct find as [[kn' mm']|] eqn:hf => //= [[<-]].
    have hin := find_some _ _ hf. cbn in hin. destruct hin as [hin heq].
    apply eqb_eq in heq. now subst.
  Qed.

  Lemma update_mib_masks_ok s kn mm :
    inds_ok P s.2 -> (P kn -> mm_ok mm) ->
    inds_ok P (update_mib_masks s kn mm).2.
  Proof.
    rewrite /update_mib_masks /=. destruct s as [s inds]; cbn.
    intros ok hmm. induction inds as [|[kn' mm'] inds IH]; cbn => //.
    destruct eq_kername.
    - intros k m [e|hin] hp; [noconf e; now apply hmm|].
      apply (ok k m); [now right|exact hp].
    - intros k m [e|hin] hp.
      + noconf e. apply (ok kn' mm'); [now left|exact hp].
      + refine (IH _ k m hin hp). intros k' m' hk. apply ok. now right.
  Qed.

  Lemma no_true_clear_bit n m : no_true m -> no_true (clear_bit n m).
  Proof.
    rewrite /no_true.
    induction n in m |- *; destruct m as [|b m]; cbn => //;
      move/andP=> [hb hm] //.
    rewrite hb /=. now apply IHn.
  Qed.

  Lemma update_ind_ctor_mask_ok ind c cms f :
    (forall m, no_true m -> no_true (f m)) ->
    forallb (fun '(_, _, m) => no_true m) cms ->
    forallb (fun '(_, _, m) => no_true m) (update_ind_ctor_mask ind c cms f).
  Proof.
    intros hf. induction cms as [|[[i' c'] m] cms IH]; cbn => //.
    move/andP=> [hm hcms].
    destruct (_ && _); cbn; rewrite ?hm ?hcms ?hf ?IH //.
  Qed.

  Lemma no_true_bitmask_and m' m : no_true m -> no_true (bitmask_and m' m).
  Proof.
    rewrite /no_true.
    induction m' in m |- *; destruct m as [|b m]; cbn => //.
    move/andP=> [hb hm]. rewrite IHm' // andb_true_r.
    destruct a, b => //.
  Qed.

  Lemma refine_ctor_mask_ok s ind c f :
    (forall m, no_true m -> no_true (f m)) ->
    inds_ok P s.2 -> inds_ok P (refine_ctor_mask s ind c f).2.
  Proof.
    intros hf ok. rewrite /refine_ctor_mask.
    destruct get_mib_masks as [mm|] eqn:hmm => //.
    apply update_mib_masks_ok => //. intros hp.
    rewrite /mm_ok /=. apply update_ind_ctor_mask_ok => //.
    exact (ok _ _ (get_mib_masks_In _ _ _ hmm) hp).
  Qed.

  Lemma fold_left_ok {A} (f : analyze_state -> A -> analyze_state) l s :
    (forall s a, In a l -> inds_ok P s.2 -> inds_ok P (f s a).2) ->
    inds_ok P s.2 -> inds_ok P (fold_left f l s).2.
  Proof.
    induction l in s |- *; cbn => // hf ok.
    apply IHl; [intros; apply hf => //; now right|].
    apply hf => //. now left.
  Qed.

  Lemma analyze_ok t s : inds_ok P s.2 -> inds_ok P (analyze s t).2.
  Proof.
    induction t using term_forall_list_ind in s |- *; cbn => //; intros ok.
    - apply fold_left_ok => //. intros s' a hin. eapply All_In in X; tea.
      destruct X as [X]. now apply X.
    - now apply IHt.
    - apply IHt2, IHt1, ok.
    - apply IHt2, IHt1, ok.
    - destruct p as [ind npars].
      have ok' := IHt s ok.
      set (f := fun c state br => _).
      have hfold : forall n s',
        inds_ok P s'.2 -> inds_ok P (fold_lefti f n l s').2.
      { clear -X. induction l as [|br l IHl]; cbn => //.
        intros n s' ok. depelim X.
        apply (IHl X (S n)). apply refine_ctor_mask_ok.
        - intros; now apply no_true_bitmask_and.
        - rewrite /remove_vars /=. apply i, ok. }
      exact (hfold 0 _ ok').
    - destruct s0 as [ind npars arg].
      apply refine_ctor_mask_ok; [|exact (IHt s ok)].
      intros; now apply no_true_clear_bit.
    - rewrite /remove_vars /=. apply fold_left_ok => //.
      intros s' d hin ok'. eapply All_In in X; tea. destruct X as [X].
      now apply X.
    - rewrite /remove_vars /=. apply fold_left_ok => //.
      intros s' d hin ok'. eapply All_In in X; tea. destruct X as [X].
      now apply X.
    - destruct p as [? []]; cbn => //; depelim X => //.
      destruct p as [hd hv]. apply fold_left_ok; [|now apply hd].
      intros s' a' hin ok'. eapply All_In in hv; tea. destruct hv as [hv].
      now apply hv.
    - now apply IHt.
    - now apply IHt.
  Qed.

  Lemma analyze_top_level_ok max_lams t s :
    inds_ok P s.2 ->
    inds_ok P (analyze_top_level analyze s max_lams t).2.2.
  Proof.
    induction t in s, max_lams |- *; intros ok; cbn [analyze_top_level];
      try exact (analyze_ok _ _ ok).
    - destruct max_lams; [exact (analyze_ok _ _ ok)|].
      have := IHt max_lams (new_var s) ok.
      destruct analyze_top_level as [mask s'] => //.
    - have := IHt2 max_lams (new_var (analyze s t1)) (analyze_ok t1 s ok).
      destruct analyze_top_level as [mask s'] => //.
  Qed.

  Lemma analyze_constant_ok cst inds :
    inds_ok P inds -> inds_ok P (analyze_constant cst inds).2.
  Proof.
    rewrite /analyze_constant. destruct decompose_TArr as [doms codom].
    destruct cst_body as [body|] => //.
    destruct analyze_top_level as [mask [s inds']] eqn:hat => ok.
    have := analyze_top_level_ok #|doms| body ([], inds) ok.
    rewrite hat /=. by destruct forallb.
  Qed.

  (** The initial masks of an inductive type. *)
  Definition init_mib_masks (mib : ExAst.mutual_inductive_body) :=
    {| param_mask := List.repeat true (ind_npars mib);
       ctor_masks := List.concat
         (mapi (fun ind oib =>
           mapi (fun c '(_, args, _) =>
             (ind, c, map (is_box_or_any ∘ snd)
               (skipn (ind_npars mib) args)))
             (ind_ctors oib))
         (ind_bodies mib)) |}.

  Lemma analyze_env_ok om (Σ : ExAst.global_env) :
    (forall kn b mib, In (kn, b, InductiveDecl mib) Σ -> P kn ->
      mm_ok (init_mib_masks mib)) ->
    inds_ok P (ind_masks (analyze_env om Σ)).
  Proof.
    induction Σ as [|[[kn b] decl] Σ IH]; cbn.
    - now intros _ ? ? [].
    - intros hdecl.
      have ok := IH (fun kn b mib hin => hdecl kn b mib (or_intror hin)).
      destruct analyze_env as [consts inds]; cbn in ok |- *.
      destruct decl as [cst|mib|ta]; cbn => //.
      + destruct analyze_constant as [mask inds'] eqn:hac.
        have := analyze_constant_ok cst inds ok. rewrite hac => //.
      + intros kn' mm [[= <- <-]|hin] hp.
        * exact (hdecl kn b mib (or_introl eq_refl) hp).
        * exact (ok kn' mm hin hp).
  Qed.

  Lemma analyze_program_ok om (Σ : ExAst.global_env) t :
    (forall kn b mib, In (kn, b, InductiveDecl mib) Σ -> P kn ->
      mm_ok (init_mib_masks mib)) ->
    inds_ok P (ind_masks (analyze_program om Σ t)).
  Proof.
    intros h. have := analyze_env_ok om Σ h.
    rewrite /analyze_program. destruct analyze_env as [cms ims]; cbn.
    apply (analyze_ok t ([], ims)).
  Qed.

  Lemma no_true_trim_end m : no_true m -> no_true (trim_end false m).
  Proof.
    rewrite /no_true /trim_end forallb_rev -(forallb_rev _ m).
    generalize (List.rev m). clear m. intros l.
    induction l as [|b l IH]; cbn => //. move/andP=> [hb hl].
    destruct b => //. cbn. now apply IH.
  Qed.

  Lemma trim_ind_masks_ok inds :
    inds_ok P inds -> inds_ok P (trim_ind_masks inds).
  Proof.
    rewrite /trim_ind_masks. intros ok kn mm hin hp.
    eapply in_map_iff in hin as [[kn' mm'] [[= <- <-] hin]].
    have := ok kn' mm' hin hp. rewrite /mm_ok /trim_mib_masks /=.
    rewrite /trim_ctor_masks forallb_map.
    eapply forallb_impl => -[[i c] m] _ /=. apply no_true_trim_end.
  Qed.

  Lemma no_true_get_branch_mask mm i c :
    mm_ok mm -> no_true (get_branch_mask mm i c).
  Proof.
    rewrite /get_branch_mask /mm_ok.
    destruct find as [[[i' c'] m]|] eqn:hf => // hok.
    have [hin _] := find_some _ _ hf.
    now eapply forallb_forall in hok; tea.
  Qed.
End AnalyzeOk.

(** ** Dearging of first-order values *)

(** The first-order values whose constructors belong to inductive types
    satisfying [P]. *)
Inductive fo_evalue_in (P : kername -> Prop) (Σ : EAst.global_declarations) :
  EAst.term -> Prop :=
| fo_evalue_in_C i n args npars nargs :
  EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (npars, nargs) ->
  P (inductive_mind i) ->
  Forall (fo_evalue_in P Σ) (skipn npars args) ->
  #|args| = npars + nargs ->
  fo_evalue_in P Σ (EAst.mkApps (EAst.tConstruct i n []) args).

Lemma fo_evalue_in_elim P Σ (Q : EAst.term -> Prop) :
  (forall i n args npars nargs,
    EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (npars, nargs) ->
    P (inductive_mind i) ->
    Forall (fo_evalue_in P Σ) (skipn npars args) ->
    Forall Q (skipn npars args) ->
    #|args| = npars + nargs ->
    Q (EAst.mkApps (EAst.tConstruct i n []) args)) ->
  forall t, fo_evalue_in P Σ t -> Q t.
Proof.
  intros H. fix aux 2. intros t [i n args npars nargs hl hp hargs hlen].
  eapply H; tea. clear hl hlen. induction hargs; constructor; auto.
Qed.

Lemma fo_evalue_in_firstorder P Σ t :
  fo_evalue_in P Σ t -> firstorder_evalue Σ t.
Proof.
  move: t; apply: fo_evalue_in_elim => i n args npars nargs hl _ _ ih hlen.
  econstructor; tea.
Qed.

(** The compilation of first-order values to constructors-as-blocks
    without parameters, on a plain environment. *)
Fixpoint cstrip (Σ : EAst.global_declarations) (t : EAst.term)
  (acc : list EAst.term) :=
  match t with
  | EAst.tApp f a => cstrip Σ f (cstrip Σ a [] :: acc)
  | EAst.tConstruct i n _ =>
    match EGlobalEnv.lookup_inductive_pars Σ (inductive_mind i) with
    | Some npars => EAst.tConstruct i n (skipn npars acc)
    | None => EAst.tVar "error"
    end
  | _ => EAst.tVar "error"
  end.

Lemma cstrip_mkApps Σ i n ui args acc npars :
  EGlobalEnv.lookup_inductive_pars Σ (inductive_mind i) = Some npars ->
  cstrip Σ (EAst.mkApps (EAst.tConstruct i n ui) args) acc =
  EAst.tConstruct i n
    (skipn npars (List.map (fun a => cstrip Σ a []) args ++ acc)).
Proof.
  revert acc; induction args using rev_ind.
  - intros acc. cbn. intros ->. auto.
  - intros acc hl. rewrite EAstUtils.mkApps_app /=.
    now rewrite IHargs // map_app /= -app_assoc /=.
Qed.

Lemma compile_evalue_box_strip_cstrip (Σ : EEnvMap.GlobalContextMap.t) t acc :
  ERemoveParams.compile_evalue_box_strip Σ t acc =
  cstrip (EEnvMap.GlobalContextMap.global_decls Σ) t acc.
Proof.
  induction t in acc |- *; cbn => //.
  - now rewrite IHt2 IHt1.
  - now rewrite EEnvMap.GlobalContextMap.lookup_env_spec.
Qed.

Lemma masked_no_true {A} m (l : list A) : no_true m -> masked m l = l.
Proof.
  induction m as [|b m IH] in l |- *; cbn => //.
  move/andP=> [hb hm]. destruct l as [|x l] => //.
  destruct b => //. now rewrite IH.
Qed.

Lemma lookup_constructor_pars_args_trans_env (Σ : ExAst.global_env) i n
  npars nargs :
  EGlobalEnv.lookup_constructor_pars_args (trans_env Σ) i n =
    Some (npars, nargs) ->
  exists mib oib ctor,
    ExAst.lookup_env Σ (inductive_mind i) = Some (InductiveDecl mib) /\
    nth_error (ExAst.ind_bodies mib) (inductive_ind i) = Some oib /\
    nth_error (ExAst.ind_ctors oib) n = Some ctor /\
    npars = ExAst.ind_npars mib /\ nargs = ctor.2.
Proof.
  rewrite /EGlobalEnv.lookup_constructor_pars_args
    /EGlobalEnv.lookup_constructor /EGlobalEnv.lookup_inductive
    /EGlobalEnv.lookup_minductive lookup_env_trans_env.
  destruct ExAst.lookup_env as [[]|] => //=.
  rewrite nth_error_map. destruct nth_error as [oib|] eqn:hoib => //=.
  rewrite /trans_ctors nth_error_map.
  destruct (nth_error (ExAst.ind_ctors oib) n) as [[[na args] ar]|] eqn:hc
    => //= [[<- <-]].
  now do 3 eexists.
Qed.

Section DeargFO.
  Context (im : list (kername × mib_masks)) (cm : list (kername × bitmask)).
  Context (P : kername -> Prop).
  Context (hok : forall kn mm, get_mib_masks im kn = Some mm -> P kn ->
    mm_ok mm).

  Lemma valid_masks_env_ind (Σ : ExAst.global_env) kn mib :
    valid_masks_env im cm Σ ->
    ExAst.lookup_env Σ kn = Some (InductiveDecl mib) ->
    exists mm, get_mib_masks im kn = Some mm /\
      #|param_mask mm| = ExAst.ind_npars mib /\
      forallbi (check_oib_masks mm) 0 (ExAst.ind_bodies mib).
  Proof.
    rewrite /valid_masks_env => hv hl.
    eapply forallb_Forall in hv.
    destruct (lookup_env_Forall _ _ _ hl hv) as [b hb].
    cbn in hb. destruct get_mib_masks as [mm|] => //.
    move/andP: hb => [/Nat.eqb_eq hp hb]. now exists mm.
  Qed.
  Lemma forallbi_nth {A} (f : nat -> A -> bool) k l j x :
    forallbi f k l -> nth_error l j = Some x -> f (k + j) x.
  Proof.
    induction l in k, j |- *; destruct j; cbn => //.
    - move/andP=> [hf _] [= <-]. now rewrite Nat.add_0_r.
    - move/andP=> [_ hl] hj. rewrite -Nat.add_succ_comm. now apply IHl.
  Qed.

  Lemma dearg_fo_evalue (Σ : ExAst.global_env) v :
    valid_masks_env im cm Σ ->
    fo_evalue_in P (trans_env Σ) v ->
    fo_evalue_in P (trans_env (Optimize.dearg_env im cm Σ)) (dearg im cm v) /\
    cstrip (trans_env (Optimize.dearg_env im cm Σ)) (dearg im cm v) [] =
    cstrip (trans_env Σ) v [].
  Proof.
    intros hv. move: v; apply: fo_evalue_in_elim.
    intros i n args npars nargs hl hp _ IH hlen.
    have [mib [oib [ctor [hmib [hoib [hctor [hn ha]]]]]]] :=
      lookup_constructor_pars_args_trans_env _ _ _ _ _ hl.
    subst npars nargs.
    have [mm [hmm [hpm hchk]]] := valid_masks_env_ind _ _ _ hv hmib.
    have hbm := no_true_get_branch_mask mm (inductive_ind i) n
      (hok _ _ hmm hp).
    have hc := forallbi_nth _ _ _ _ _ hchk hoib. cbn in hc.
    move/andP: hc => [hc _].
    have hlb := forallbi_nth _ _ _ _ _ hc hctor. cbn in hlb.
    apply eqb_eq in hlb.
    rewrite dearg_mkApps /= /get_ctor_mask hmm.
    set (bm := get_branch_mask mm _ n) in *.
    set (pm := param_mask mm) in *.
    rewrite dearg_single_masked; [len|].
    rewrite masked_app (masked_no_true bm) //.
    have hco : count_ones bm = 0.
    { clear -hbm. rewrite /count_ones.
      induction bm as [|b bm IH]; cbn in * => //.
      move/andP: hbm => [hb hbm]. destruct b => //. now apply IH. }
    destruct ctor as [[na fields] ar]. cbn in hlb, hlen, IH |- *.
    have hl' : EGlobalEnv.lookup_constructor_pars_args
      (trans_env (Optimize.dearg_env im cm Σ)) i n =
      Some (count_zeros pm, ar).
    { rewrite /EGlobalEnv.lookup_constructor_pars_args
        /EGlobalEnv.lookup_constructor /EGlobalEnv.lookup_inductive
        /EGlobalEnv.lookup_minductive lookup_env_trans_env
        lookup_env_dearg_env hmib /=.
      rewrite /dearg_mib hmm /= nth_error_map nth_error_mapi hoib /=.
      rewrite /trans_ctors nth_error_map nth_error_mapi hctor /=.
      now rewrite hco Nat.sub_0_r. }
    have hlp' : EGlobalEnv.lookup_inductive_pars
      (trans_env (Optimize.dearg_env im cm Σ)) (inductive_mind i) =
      Some (count_zeros pm).
    { rewrite /EGlobalEnv.lookup_inductive_pars
        /EGlobalEnv.lookup_minductive lookup_env_trans_env
        lookup_env_dearg_env hmib /=.
      now rewrite /dearg_mib hmm /=. }
    have hlp : EGlobalEnv.lookup_inductive_pars (trans_env Σ)
      (inductive_mind i) = Some (ind_npars mib).
    { rewrite /EGlobalEnv.lookup_inductive_pars
        /EGlobalEnv.lookup_minductive lookup_env_trans_env hmib /=.
      reflexivity. }
    have hfl : #|firstn (count_zeros pm)
      (masked pm (map (dearg im cm) args))| = count_zeros pm.
    { rewrite length_firstn masked_length; len. }
    rewrite hpm. split.
    - econstructor; tea.
      + rewrite skipn_all_app_eq // -map_skipn. apply Forall_map.
        eapply Forall_impl; tea. now intros x [].
      + len. rewrite hfl length_skipn. lia.
    - rewrite (cstrip_mkApps _ _ _ _ _ _ _ hlp')
        (cstrip_mkApps _ _ _ _ _ _ _ hlp).
      f_equal. rewrite !app_nil_r map_app skipn_all_app_eq; len.
      rewrite -map_skipn map_map -!map_skipn. apply map_ext_Forall.
      eapply Forall_impl; tea. now intros x [].
  Qed.
End DeargFO.

(** ** Typed erasure of first-order constructor types *)

From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
  PCUICReduction PCUICWellScopedCumulativity PCUICConversion
  PCUICInductiveInversion PCUICSN PCUICLiftSubst PCUICUnivSubst
  PCUICWeakeningEnvTyp PCUICUnivSubstitutionConv PCUICContextConversion
  PCUICFirstorder.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICSafeReduce
  PCUICSafeRetyping.
From MetaRocq.Erasure.Typed Require Erasure.

#[local] Existing Instance config.extraction_checker_flags.

(** A sort reached by reduction from an arity is its sort. *)
Lemma red_it_mkProd_or_LetIn_sort {Σ : global_env_ext} {wfΣ : wf Σ} Γ ctx s
  u :
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx (tSort s) ⇝ tSort u -> u = s.
Proof.
  induction ctx as [|d ctx IH] using PCUICInduction.ctx_length_rev_ind
    in Γ, s |- *.
  - cbn. intros r. eapply invert_red_sort in r. now noconf r.
  - rewrite it_mkProd_or_LetIn_app /=.
    destruct d as [na [b|] ty]; cbn.
    + intros r. eapply invert_red_letin in r as [[d' [ty' [b' []]]]|r] => //.
      rewrite /subst1 subst_it_mkProd_or_LetIn /= in r.
      eapply (IH (subst_context [b] 0 ctx)); [now len|exact r].
    + intros r. eapply invert_red_prod in r as [dom' [codom' []]] => //.
Qed.

Lemma infering_tRel_inv {Σ : global_env_ext} Γ n K decl :
  BDTyping.infering Σ Γ (tRel n) K -> nth_error Γ n = Some decl ->
  K = lift0 (S n) (decl_type decl).
Proof.
  intros h hn. depelim h. rewrite hn in e. now noconf e.
Qed.

Lemma In_map_In {A B} (l : list A) (f : forall x, In x l -> B) y :
  In y (map_In l f) -> exists x (h : In x l), y = f x h.
Proof.
  funelim (map_In l f); cbn => //.
  intros [<-|hin]; [now eexists _, _|].
  destruct (H _ hin) as [x' [h' ->]]. now exists x', (or_intror h').
Qed.

Lemma mm_ok_intro (mib : ExAst.mutual_inductive_body) :
  (forall oib ctor x, In oib (ExAst.ind_bodies mib) ->
    In ctor (ExAst.ind_ctors oib) -> In x ctor.1.2 ->
    is_box_or_any x.2 = false) ->
  mm_ok (init_mib_masks mib).
Proof.
  intros h. rewrite /mm_ok /init_mib_masks /=.
  apply forallb_forall => -[[i c] m] hin.
  apply in_concat in hin as [l [hl hin]].
  apply In_nth_error in hl as [ii hl]. rewrite nth_error_mapi in hl.
  destruct nth_error as [oib|] eqn:hoib => //. cbn in hl. noconf hl.
  apply In_nth_error in hin as [cc hc]. rewrite nth_error_mapi in hc.
  destruct (nth_error (ExAst.ind_ctors oib) cc) as [[[na args] ar]|] eqn:hct
    => //.
  cbn in hc. noconf hc.
  rewrite /no_true forallb_map. apply forallb_forall => x hx.
  apply ErasureFunction.In_skipn in hx. cbn.
  rewrite (h oib (na, args, ar) x) //; now eapply nth_error_In.
Qed.

Definition arities_inv (S : list one_inductive_body) (Γ : context)
  (erΓ : Vector.t Erasure.tRel_kind #|Γ|) :=
  forall j, j < #|Γ| ->
    (exists ind, forall h : j < #|Γ|,
      Vector.nth_order erΓ h = Erasure.RelInductive ind) /\
    exists decl oib, nth_error Γ j = Some decl /\ decl_body decl = None /\
      decl_type decl = ind_type oib /\ In oib S.

Lemma arities_contexts_inv kn oibs :
  arities_inv oibs (Erasure.arities_contexts kn oibs).π1
    (Erasure.arities_contexts kn oibs).π2.
Proof.
  unfold Erasure.arities_contexts.
  match goal with |- arities_inv _ (?f' _ _ _ _).π1 _ => set (f := f') end.
  enough (H : forall l i Γ erΓ, incl l oibs -> arities_inv oibs Γ erΓ ->
    arities_inv oibs (f l i Γ erΓ).π1 (f l i Γ erΓ).π2).
  { apply H; [now intros x|]. intros j hj. cbn in hj. lia. }
  induction l as [|oib l IH]; intros i Γ erΓ hincl hinv; cbn => //.
  apply IH; [intros x hx; apply hincl; now right|].
  intros [|j] hj.
  - split; [now eexists|].
    exists (vass (Erasure.ind_aname oib) (ind_type oib)), oib.
    repeat split => //. apply hincl. now left.
  - cbn in hj. destruct (hinv j ltac:(lia)) as [[ind hind] hdecl].
    split; [|exact hdecl].
    exists ind. intros h.
    have hj' : j < #|Γ| by lia.
    rewrite -(hind hj').
    change (S j < S #|Γ|) in h.
    exact (eq_sym (Vector.nth_order_tl _ _ _ (Vector.cons _ _ _ erΓ) hj' h)).
Qed.

Section TypedFO.
  Context {X_type : abstract_env_impl} {X : X_type.π2.π1}
    {no : normalizing_flags}
    {normalization_in :
      forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.
  Context (rΣ : global_env_ext) (wfrΣ : rΣ ∼_ext X).

  Lemma flag_of_type_tInd Γ ind u isT :
    (forall mdecl idecl, declared_inductive rΣ ind mdecl idecl ->
      Sort.is_prop (ind_sort idecl) = false) ->
    exists p : ~ ∥ Erasure.conv_arity rΣ Γ (tInd ind u) ∥,
      Erasure.flag_of_type rΣ wfrΣ Γ (tInd ind u) isT =
      Erasure.build_flag _ _ _ false (inr p).
  Proof.
    intros hsort.
    have [wfΣ] := abstract_env_ext_wf X wfrΣ.
    rewrite Erasure.flag_of_type_equation_1.
    destruct (ErasureFunction.inspect _) as [T0 e]. cbn.
    have heq : T0 = tInd ind u.
    { pose proof (reduce_term_sound PCUICNormal.RedFlags.default X_type X Γ
        (tInd ind u) (fun Σ h => Erasure.tywt (isT Σ h)) rΣ wfrΣ) as [r].
      unfold hnf in e. rewrite e in r.
      have [args' [-> _ hargs]] :=
        invert_red_mkApps_tInd (Σ := rΣ) (wfΣ := wfΣ) [] _ r.
      now depelim hargs. }
    subst T0. rewrite Erasure.flag_of_type_clause_1_clause_1_equation_3.
    match goal with |- context [infer ?a ?b ?c ?d ?e ?f] =>
      destruct (infer a b c d e f) as [K princK] end.
    rewrite Erasure.flag_of_type_clause_1_clause_1_clause_3_equation_1.
    destruct (ErasureFunction.inspect _) as [[[univ hred]|err] eqs].
    - rewrite
        Erasure.flag_of_type_clause_1_clause_1_clause_3_clause_1_equation_1.
      eexists. f_equal.
      have [princ] := princK rΣ wfrΣ. rewrite heq in princ.
      depelim princ.
      have [r] := hred rΣ wfrΣ.
      have [_ onind] := on_declared_inductive (wfΣ := wfΣ) isdecl.
      rewrite (ind_arity_eq onind) !subst_instance_it_mkProd_or_LetIn
        -it_mkProd_or_LetIn_app /= in r.
      eapply red_it_mkProd_or_LetIn_sort in r. subst univ.
      rewrite is_prop_subst_instance_univ. now eapply hsort.
    - rewrite
        Erasure.flag_of_type_clause_1_clause_1_clause_3_clause_1_equation_2.
      match goal with |- context [False_rect _ ?p] => destruct p end.
  Qed.
  Lemma flag_of_type_clause_tRel Γ T isT n decl ctx s e :
    nth_error Γ n = Some decl ->
    decl_type decl = it_mkProd_or_LetIn ctx (tSort s) ->
    Sort.is_prop s = false ->
    exists p : ~ ∥ Erasure.conv_arity rΣ Γ T ∥,
      Erasure.flag_of_type_unfold_clause_1_clause_1 rΣ wfrΣ Γ T isT (tRel n)
        (Erasure.fot_viewc (tRel n)) e =
      Erasure.build_flag _ _ _ false (inr p).
  Proof.
    intros hn hty hs.
    rewrite Erasure.flag_of_type_clause_1_clause_1_equation_3.
    match goal with |- context [infer ?a ?b ?c ?d ?e ?f] =>
      destruct (infer a b c d e f) as [K princK] end.
    rewrite Erasure.flag_of_type_clause_1_clause_1_clause_3_equation_1.
    destruct (ErasureFunction.inspect _) as [[[univ hred]|err] eqs].
    - rewrite
        Erasure.flag_of_type_clause_1_clause_1_clause_3_clause_1_equation_1.
      eexists. f_equal.
      have [princ] := princK rΣ wfrΣ.
      have [r] := hred rΣ wfrΣ.
      have [wfΣ] := abstract_env_ext_wf X wfrΣ.
      rewrite (infering_tRel_inv _ _ _ _ princ hn) hty
        lift_it_mkProd_or_LetIn /= in r.
      eapply red_it_mkProd_or_LetIn_sort in r. now subst univ.
    - rewrite
        Erasure.flag_of_type_clause_1_clause_1_clause_3_clause_1_equation_2.
      match goal with |- context [False_rect _ ?p] => destruct p end.
  Qed.

  Lemma reduce_term_tRel flags Γ n decl h :
    nth_error Γ n = Some decl -> decl_body decl = None ->
    reduce_term flags X_type X Γ (tRel n) h = tRel n.
  Proof.
    intros hn hb.
    have [wfΣ] := abstract_env_ext_wf X wfrΣ.
    pose proof (reduce_term_sound flags X_type X Γ (tRel n) h rΣ wfrΣ)
      as [r].
    have [args' [e hargs]] :=
      invert_red_mkApps_tRel (wfΣ := wfΣ) (args := []) hn hb r.
    depelim hargs. exact e.
  Qed.

  Lemma reduce_term_tInd flags Γ ind u h :
    reduce_term flags X_type X Γ (tInd ind u) h = tInd ind u.
  Proof.
    have [wfΣ] := abstract_env_ext_wf X wfrΣ.
    pose proof (reduce_term_sound flags X_type X Γ (tInd ind u) h rΣ wfrΣ)
      as [r].
    have [args' [e _ hargs]] :=
      invert_red_mkApps_tInd (Σ := rΣ) (wfΣ := wfΣ) [] _ r.
    depelim hargs. exact e.
  Qed.

  Lemma flag_of_type_tRel Γ n decl ctx s isT :
    nth_error Γ n = Some decl -> decl_body decl = None ->
    decl_type decl = it_mkProd_or_LetIn ctx (tSort s) ->
    Sort.is_prop s = false ->
    exists p : ~ ∥ Erasure.conv_arity rΣ Γ (tRel n) ∥,
      Erasure.flag_of_type rΣ wfrΣ Γ (tRel n) isT =
      Erasure.build_flag _ _ _ false (inr p).
  Proof.
    intros hn hb hty hs.
    have [wfΣ] := abstract_env_ext_wf X wfrΣ.
    rewrite Erasure.flag_of_type_equation_1.
    destruct (ErasureFunction.inspect _) as [T0 e].
    rewrite Erasure.flag_of_type_clause_1_equation_1.
    have heq : T0 = tRel n.
    { rewrite -e. exact (reduce_term_tRel _ _ _ _ _ hn hb). }
    symmetry in heq. destruct heq.
    exact (flag_of_type_clause_tRel _ _ _ _ _ _ _ _ hn hty hs).
  Qed.
  Lemma erase_type_aux_tInd Γ erΓ ind u isT nt :
    (forall mdecl idecl, declared_inductive rΣ ind mdecl idecl ->
      Sort.is_prop (ind_sort idecl) = false) ->
    Erasure.erase_type_aux rΣ wfrΣ Γ erΓ (tInd ind u) isT nt =
    ([], TInd ind).
  Proof.
    intros hsort.
    rewrite Erasure.erase_type_aux_unfold_eq /Erasure.erase_type_aux_unfold.
    destruct (ErasureFunction.inspect _) as [t0 e].
    have heq : t0 = tInd ind u.
    { rewrite -e. exact (reduce_term_tInd _ _ _ _ _). }
    symmetry in heq. destruct heq.
    rewrite Erasure.erase_type_aux_clause_1_equation_1.
    match goal with |- context [Erasure.flag_of_type rΣ wfrΣ ?Γ ?T ?isT] =>
      destruct (flag_of_type_tInd Γ ind u isT hsort) as [p hp];
      rewrite hp
    end.
    reflexivity.
  Qed.

  Lemma erase_type_aux_tRel Γ (erΓ : Vector.t Erasure.tRel_kind #|Γ|) n decl
    ctx s ind isT nt :
    nth_error Γ n = Some decl -> decl_body decl = None ->
    decl_type decl = it_mkProd_or_LetIn ctx (tSort s) ->
    Sort.is_prop s = false ->
    (forall h : n < #|Γ|,
      Vector.nth_order erΓ h = Erasure.RelInductive ind) ->
    Erasure.erase_type_aux rΣ wfrΣ Γ erΓ (tRel n) isT nt = ([], TInd ind).
  Proof.
    intros hn hb hty hs her.
    rewrite Erasure.erase_type_aux_unfold_eq /Erasure.erase_type_aux_unfold.
    destruct (ErasureFunction.inspect _) as [t0 e].
    have heq : t0 = tRel n.
    { rewrite -e. exact (reduce_term_tRel _ _ _ _ _ hn hb). }
    symmetry in heq. destruct heq.
    rewrite Erasure.erase_type_aux_clause_1_equation_1.
    match goal with |- context [Erasure.flag_of_type rΣ wfrΣ ?Γ ?T ?isT] =>
      destruct (flag_of_type_tRel Γ n decl ctx s isT hn hb hty hs)
        as [p hp];
      rewrite hp
    end.
    cbn [Erasure.is_logical].
    rewrite Erasure.erase_type_aux_clause_1_clause_1_equation_2.
    rewrite Erasure.erase_type_aux_clause_1_clause_1_clause_2_equation_1.
    rewrite her.
    exact (Erasure.erase_type_aux_clause_1_clause_1_clause_2_clause_1_equation_2
      _ _ _ _ _ _ _ _).
  Qed.

  (** Argument types of first-order constructors. *)
  Definition fo_atom (Γ : context) (erΓ : Vector.t Erasure.tRel_kind #|Γ|)
    (A : term) : Prop :=
    (exists ind u, A = tInd ind u /\
      forall mdecl idecl, declared_inductive rΣ ind mdecl idecl ->
        Sort.is_prop (ind_sort idecl) = false) \/
    (exists n decl ctx s ind, A = tRel n /\ nth_error Γ n = Some decl /\
      decl_body decl = None /\
      decl_type decl = it_mkProd_or_LetIn ctx (tSort s) /\
      Sort.is_prop s = false /\
      forall h : n < #|Γ|, Vector.nth_order erΓ h = Erasure.RelInductive ind).

  Lemma erase_type_aux_atom Γ erΓ A isT nt :
    fo_atom Γ erΓ A ->
    exists ind,
      Erasure.erase_type_aux rΣ wfrΣ Γ erΓ A isT nt = ([], TInd ind).
  Proof.
    intros [[ind [u [-> hs]]]|
      [n [decl [ctx [s [ind [-> [hn [hb [hty [hs her]]]]]]]]]]].
    - exists ind. now apply erase_type_aux_tInd.
    - exists ind. eapply erase_type_aux_tRel; tea.
  Qed.

  Lemma flag_of_type_atom Γ erΓ A isT :
    fo_atom Γ erΓ A ->
    exists p : ~ ∥ Erasure.conv_arity rΣ Γ A ∥,
      Erasure.flag_of_type rΣ wfrΣ Γ A isT =
      Erasure.build_flag _ _ _ false (inr p).
  Proof.
    intros [[ind [u [-> hs]]]|
      [n [decl [ctx [s [ind [-> [hn [hb [hty [hs her]]]]]]]]]]].
    - now apply flag_of_type_tInd.
    - eapply flag_of_type_tRel; tea.
  Qed.

  (** Types whose products all have first-order domains, up to
      reduction. *)
  Inductive fo_spine (Γ : context) (erΓ : Vector.t Erasure.tRel_kind #|Γ|)
    (t : term) : Prop :=
  | fo_spine_intro :
    (forall na A B, rΣ ;;; Γ ⊢ t ⇝ tProd na A B -> fo_atom Γ erΓ A) ->
    (forall na A B, rΣ ;;; Γ ⊢ t ⇝ tProd na A B ->
      forall k, fo_spine (Γ ,, vass na A) (Vector.cons _ k _ erΓ) B) ->
    fo_spine Γ erΓ t.

  Lemma decompose_arr_mkTApps h l :
    match h with TArr _ _ => false | _ => true end = true ->
    (decompose_arr (mkTApps h l)).1 = [].
  Proof.
    induction l in h |- *; cbn.
    - destruct h => //.
    - intros _. now apply IHl.
  Qed.

  Lemma decompose_arr_if_can h l :
    match h with TArr _ _ => false | _ => true end = true ->
    (decompose_arr
      (if can_have_args h then (@nil name, mkTApps h l) else ([], h)).2).1 = [].
  Proof.
    intros hna. destruct can_have_args; cbn [snd].
    - now apply decompose_arr_mkTApps.
    - exact (decompose_arr_mkTApps h [] hna).
  Qed.

  Lemma erase_type_aux_fo_spine Γ erΓ t isT nt :
    fo_spine Γ erΓ t ->
    forallb (negb ∘ is_box_or_any)
      (decompose_arr (Erasure.erase_type_aux rΣ wfrΣ Γ erΓ t isT nt).2).1.
  Proof.
    intros fs. induction fs in isT, nt |- *.
    rewrite Erasure.erase_type_aux_unfold_eq /Erasure.erase_type_aux_unfold.
    destruct (ErasureFunction.inspect _) as [t0 e].
    rewrite Erasure.erase_type_aux_clause_1_equation_1.
    destruct (Erasure.is_logical _) eqn:hl.
    - rewrite Erasure.erase_type_aux_clause_1_clause_1_equation_1. reflexivity.
    - rewrite Erasure.erase_type_aux_clause_1_clause_1_equation_2.
      destruct (Erasure.erase_type_viewc t0).
      1:rewrite Erasure.erase_type_aux_clause_1_clause_1_clause_2_equation_1.
      2:rewrite Erasure.erase_type_aux_clause_1_clause_1_clause_2_equation_2.
      3:rewrite Erasure.erase_type_aux_clause_1_clause_1_clause_2_equation_3.
      4:rewrite Erasure.erase_type_aux_clause_1_clause_1_clause_2_equation_4.
      5:rewrite Erasure.erase_type_aux_clause_1_clause_1_clause_2_equation_5.
      6:rewrite Erasure.erase_type_aux_clause_1_clause_1_clause_2_equation_6.
      7:rewrite Erasure.erase_type_aux_clause_1_clause_1_clause_2_equation_7.
      all: try reflexivity.
      + destruct (Vector.nth_order _ _); reflexivity.
      + have [wfΣ] := abstract_env_ext_wf X wfrΣ.
        pose proof (reduce_term_sound PCUICNormal.RedFlags.nodelta X_type X Γ
          t (fun Σ h => Erasure.tywt (isT Σ h)) rΣ wfrΣ) as [r].
        rewrite e in r.
        have hA := H _ _ _ r.
        match goal with
        | |- context [Erasure.flag_of_type rΣ wfrΣ ?Γ ?T ?isT] =>
          destruct (flag_of_type_atom Γ erΓ T isT hA) as [p hp]; rewrite hp
        end.
        first
          [rewrite
          Erasure.erase_type_aux_clause_1_clause_1_clause_2_clause_3_equation_2
          |rewrite
          Erasure.erase_type_aux_clause_1_clause_1_clause_2_clause_3_equation_3
          ].
        match goal with
        |- context [Erasure.erase_type_aux rΣ wfrΣ Γ erΓ A ?isA None] =>
          destruct (erase_type_aux_atom Γ erΓ A isA None hA) as [ind hi];
          rewrite hi
        end.
        cbv beta iota.
        match goal with
        |- context [Erasure.erase_type_aux rΣ wfrΣ (Γ,, vass na A) ?er B ?isB
            nt] =>
          have ih := H1 _ _ _ r Erasure.RelOther isB nt;
          destruct
            (Erasure.erase_type_aux rΣ wfrΣ (Γ,, vass na A) er B isB nt)
            as [tvs cod]
        end.
        cbn in ih |- *. destruct (decompose_arr cod) as [args res].
        exact ih.
      + destruct (ErasureFunction.inspect _) as [[hd' args'] eqd].
        rewrite
          Erasure.erase_type_aux_clause_1_clause_1_clause_2_clause_4_equation_1.
        cbv zeta.
        match goal with
        |- context [if can_have_args ?h then ([], mkTApps _ ?l) else _] =>
          let hna := fresh "hna" in
          assert (hna : match h with TArr _ _ => false | _ => true end = true);
          [destruct hd'; try reflexivity; destruct Vector.nth_order;
            reflexivity
          |rewrite (decompose_arr_if_can h l hna); reflexivity]
        end.
  Qed.

  Lemma erase_ind_ctor_fo_spine Γ erΓ t isT np tvars :
    fo_spine Γ erΓ t ->
    forallb (negb ∘ is_box_or_any)
      (decompose_arr
        (Erasure.erase_ind_ctor rΣ wfrΣ Γ erΓ t isT np tvars)).1.
  Proof.
    induction tvars as [|tv tvars IH] in Γ, erΓ, t, isT, np |- *; intros fs.
    - rewrite Erasure.erase_ind_ctor_equation_1.
      now apply erase_type_aux_fo_spine.
    - rewrite Erasure.erase_ind_ctor_equation_2.
      destruct (ErasureFunction.inspect _) as [t0 e].
      rewrite Erasure.erase_ind_ctor_clause_2_equation_1.
      destruct (Erasure.view_prodc t0).
      + rewrite Erasure.erase_ind_ctor_clause_2_clause_1_equation_1.
        have [wfΣ] := abstract_env_ext_wf X wfrΣ.
        pose proof (reduce_term_sound PCUICNormal.RedFlags.nodelta X_type X Γ
          t (fun Σ h => Erasure.tywt (isT Σ h)) rΣ wfrΣ) as [r].
        rewrite e in r.
        destruct fs as [hA hB]. have hA' := hA _ _ _ r.
        match goal with
        |- context [Erasure.erase_type_aux rΣ wfrΣ Γ erΓ A ?isA None] =>
          destruct (erase_type_aux_atom Γ erΓ A isA None hA') as [ind hi];
          rewrite hi
        end.
        cbv beta iota zeta.
        match goal with
        |- context [Erasure.erase_ind_ctor rΣ wfrΣ (Γ,, vass na A) ?er B ?isB
            (S np) tvars] =>
          have ih := IH (Γ,, vass na A) er B isB (S np) (hB _ _ _ r _)
        end.
        revert ih. cbn [decompose_arr].
        destruct (decompose_arr _) as [args res]. cbn. now intros ->.
      + rewrite Erasure.erase_ind_ctor_clause_2_clause_1_equation_2.
        reflexivity.
  Qed.
  (** ** Syntactic first-order constructor types

    Under a context made of [n] arities followed by [k] binders, the
    domains are first-order inductive types or one of the arities, and the
    conclusion is headed by one of the arities. *)

  Definition ind_nonprop ind :=
    forall mdecl idecl, declared_inductive rΣ ind mdecl idecl ->
      Sort.is_prop (ind_sort idecl) = false.

  Definition sfo_atom n k A :=
    (exists ind u, A = tInd ind u /\ ind_nonprop ind) \/
    (exists i, A = tRel i /\ k <= i /\ i < k + n).

  Inductive sfo_ty (n : nat) : nat -> term -> Prop :=
  | sfo_concl k j args : k <= j -> j < k + n ->
    sfo_ty n k (mkApps (tRel j) args)
  | sfo_prod k na A B : sfo_atom n k A -> sfo_ty n (S k) B ->
    sfo_ty n k (tProd na A B)
  | sfo_let k na b ty B : sfo_ty n (S k) B -> sfo_ty n k (tLetIn na b ty B).

  Fixpoint nbinders (t : term) :=
    match t with
    | tProd _ _ B | tLetIn _ _ _ B => S (nbinders B)
    | _ => 0
    end.

  Lemma nbinders_mkApps_tRel j args : nbinders (mkApps (tRel j) args) = 0.
  Proof. destruct args using rev_case => //. now rewrite mkApps_app. Qed.

  Lemma sfo_ty_subst n k m b T :
    sfo_ty n (S k + m) T ->
    sfo_ty n (k + m) (subst [b] m T) /\
    nbinders (subst [b] m T) = nbinders T.
  Proof.
    remember (S k + m) as k' eqn:ek. intros h.
    induction h in m, ek |- *; subst.
    - rewrite subst_mkApps.
      have e : subst [b] m (tRel j) = tRel (j - 1).
      { cbn. destruct (Nat.leb_spec m j); [|lia].
        replace (j - m) with (S (j - S m)) by lia. cbn.
        now rewrite nth_error_nil. }
      rewrite e !nbinders_mkApps_tRel. split; [constructor; lia|reflexivity].
    - destruct (IHh (S m) ltac:(lia)) as [IH1 IH2]. cbn. split; [|now f_equal].
      constructor.
      + destruct H as [[ind [u [-> hi]]]|[i [-> [hi hi']]]].
        * left. now exists ind, u.
        * right. cbn. destruct (Nat.leb_spec m i); [|lia].
          replace (i - m) with (S (i - S m)) by lia. cbn.
          rewrite nth_error_nil. eexists; split; [reflexivity|lia].
      + now replace (k + S m) with (S (k + m)) in IH1 by lia.
    - destruct (IHh (S m) ltac:(lia)) as [IH1 IH2]. cbn. split; [|now f_equal].
      constructor. now replace (k + S m) with (S (k + m)) in IH1 by lia.
  Qed.

  Definition ar_ok (Γ : context) (erΓ : Vector.t Erasure.tRel_kind #|Γ|)
    k n :=
    forall i, k <= i -> i < k + n ->
    exists decl ctx s ind, nth_error Γ i = Some decl /\
      decl_body decl = None /\
      decl_type decl = it_mkProd_or_LetIn ctx (tSort s) /\
      Sort.is_prop s = false /\
      forall h : i < #|Γ|, Vector.nth_order erΓ h = Erasure.RelInductive ind.

  Lemma ar_ok_cons Γ erΓ k n d x :
    ar_ok Γ erΓ k n -> ar_ok (Γ ,, d) (Vector.cons _ x _ erΓ) (S k) n.
  Proof.
    intros ok i hi hi'. destruct i as [|i]; [lia|].
    destruct (ok i ltac:(lia) ltac:(lia)) as
      [decl [ctx [s [ind [hn [hb [hty [hs her]]]]]]]].
    exists decl, ctx, s, ind. repeat split => //.
    intros h. have h' : i < #|Γ| by (cbn in h; lia).
    rewrite -(her h').
    change (S i < S #|Γ|) in h.
    exact (eq_sym (Vector.nth_order_tl _ _ _ (Vector.cons _ x _ erΓ) h' h)).
  Qed.

  Lemma sfo_atom_fo_atom Γ erΓ k n A :
    ar_ok Γ erΓ k n -> sfo_atom n k A -> fo_atom Γ erΓ A.
  Proof.
    intros ok [[ind [u [-> hi]]]|[i [-> [hi hi']]]].
    - left. now exists ind, u.
    - right. destruct (ok i hi hi') as [decl [ctx [s [ind h]]]].
      now exists i, decl, ctx, s, ind.
  Qed.

  Lemma fo_atom_red Γ erΓ A A' :
    fo_atom Γ erΓ A -> rΣ ;;; Γ ⊢ A ⇝ A' -> A' = A.
  Proof.
    have [wfΣ] := abstract_env_ext_wf X wfrΣ.
    intros [[ind [u [-> _]]]|[n [decl [ctx [s [ind [-> [hn [hb _]]]]]]]]] r.
    - have [args' [-> _ hargs]] :=
        invert_red_mkApps_tInd (Σ := rΣ) (wfΣ := wfΣ) [] _ r.
      now depelim hargs.
    - have [args' [-> hargs]] :=
        invert_red_mkApps_tRel (wfΣ := wfΣ) (args := []) hn hb r.
      now depelim hargs.
  Qed.

  Lemma fo_spine_red Γ erΓ t t' :
    fo_spine Γ erΓ t -> rΣ ;;; Γ ⊢ t ⇝ t' -> fo_spine Γ erΓ t'.
  Proof.
    intros [hA hB] r. constructor.
    - intros na A B r'. apply (hA na A B). now transitivity t'.
    - intros na A B r'. apply (hB na A B). now transitivity t'.
  Qed.

  Lemma sfo_ty_fo_spine n k T Γ erΓ :
    sfo_ty n k T -> ar_ok Γ erΓ k n -> fo_spine Γ erΓ T.
  Proof.
    have [wfΣ] := abstract_env_ext_wf X wfrΣ.
    remember (nbinders T) as nb eqn:enb.
    induction nb as [nb IH] using (well_founded_induction lt_wf)
      in T, k, Γ, erΓ, enb |- *.
    intros h ok. destruct h.
    - constructor; intros na A B r.
      all: destruct (ok j H H0) as [decl [ctx [s [ind [hn [hb _]]]]]].
      all: have [args' [e _]] :=
        invert_red_mkApps_tRel (wfΣ := wfΣ) hn hb r.
      all: destruct args' using rev_case; [discriminate e|].
      all: rewrite mkApps_app in e; discriminate e.
    - have hA := sfo_atom_fo_atom _ _ _ _ _ ok H.
      constructor; intros na' A' B' r;
        eapply invert_red_prod in r as [dom' [codom' [e rA rB]]].
      all: injection e as -> -> ->.
      all: have eA := fo_atom_red _ _ _ _ hA rA; subst dom'.
      + exact hA.
      + intros x. eapply fo_spine_red; [|exact rB].
        eapply (IH (nbinders B)); [cbn in enb; lia|reflexivity|exact h|].
        now apply ar_ok_cons.
    - constructor; intros na' A' B' r;
        eapply invert_red_letin in r as [[d' [ty' [b' [e _ _ _]]]]|r];
        try discriminate.
      all: destruct (sfo_ty_subst n k 0 b B) as [hs hnb];
        [now rewrite Nat.add_0_r|].
      all: rewrite Nat.add_0_r in hs.
      all: have fs := IH (nbinders (subst [b] 0 B)) ltac:(cbn in enb; lia)
        _ _ _ _ eq_refl hs ok.
      all: destruct fs as [fA fB].
      + exact (fA _ _ _ r).
      + exact (fB _ _ _ r).
  Qed.
  (** The initial dearging masks of a block whose constructor types are
      first-order spines remove nothing. *)
  Lemma erase_ind_mm_ok kn mib wt :
    (forall oib c, In oib (PCUICEnvironment.ind_bodies mib) ->
      In c (PCUICEnvironment.ind_ctors oib) ->
      fo_spine
        (Erasure.arities_contexts kn (PCUICEnvironment.ind_bodies mib)).π1
        (Erasure.arities_contexts kn (PCUICEnvironment.ind_bodies mib)).π2
        (PCUICEnvironment.cstr_type c)) ->
    mm_ok (init_mib_masks (Erasure.erase_ind rΣ wfrΣ kn mib wt)).
  Proof.
    intros hfo. apply mm_ok_intro => oibx ctor x hoib hct hx.
    cbn in hoib. apply In_map_In in hoib as [oib [hin ->]].
    rewrite /Erasure.erase_ind_body /= in hct.
    apply In_map_In in hct as [c [hc ->]].
    match type of hx with
    | context [decompose_arr
        (Erasure.erase_ind_ctor rΣ wfrΣ ?G ?E ?t ?isT 0 ?tv)] =>
      have hf := erase_ind_ctor_fo_spine G E t isT 0 tv (hfo oib c hin hc);
      destruct (decompose_arr (Erasure.erase_ind_ctor rΣ wfrΣ G E t isT 0 tv))
        as [args res]
    end.
    cbn [fst snd] in hx, hf. destruct x as [na bt].
    apply in_combine_r in hx.
    eapply forallb_forall in hf; tea. cbn. now apply negbTE in hf.
  Qed.
  Lemma sfo_it_mkProd n (P : nat -> context_decl -> bool)
    (hP : forall j d, P j d -> sfo_atom n j (decl_type d)) Δ k T :
    alli P k (List.rev Δ) -> sfo_ty n (k + #|Δ|) T ->
    sfo_ty n k (it_mkProd_or_LetIn Δ T).
  Proof.
    revert k T. induction Δ as [|d Δ IH] using rev_ind; intros k T; cbn.
    - now rewrite Nat.add_0_r.
    - rewrite rev_app_distr it_mkProd_or_LetIn_app /=.
      move/andP=> [hd hΔ] hT.
      rewrite length_app /= in hT.
      have hT' : sfo_ty n (S k + #|Δ|) T.
      { now replace (S k + #|Δ|) with (k + (#|Δ| + 1)) by lia. }
      destruct d as [na [b|] ty]; cbn; constructor.
      + now apply IH.
      + exact (hP _ _ hd).
      + now apply IH.
  Qed.

  (** Well-formed first-order constructor types are syntactically
      first-order. *)
  Lemma cstr_type_sfo Σb Σ' (mib : mutual_inductive_body) i oib idx cdecl
    cunivs :
    (forall j t, @PCUICFirstorder.firstorder_type Σb #|ind_bodies mib| j t ->
      sfo_atom #|ind_bodies mib| j t) ->
    on_constructor cumulSpec0 (lift_typing typing) Σ' mib i oib idx cdecl
      cunivs ->
    i < #|ind_bodies mib| ->
    @PCUICFirstorder.firstorder_con Σb mib cdecl ->
    sfo_ty #|ind_bodies mib| 0 (cstr_type cdecl).
  Proof.
    intros hft oc hi hfo.
    rewrite (cstr_eq oc) -it_mkProd_or_LetIn_app.
    eapply sfo_it_mkProd; [|exact hfo|].
    - intros j [na b t]. cbn. apply hft.
    - rewrite /cstr_concl /cstr_concl_head. constructor; len; lia.
  Qed.

  (** The typed erasure of a well-formed first-order block gives initial
      dearging masks that remove nothing. *)
  Lemma erase_ind_fo_mm_ok Σb kn mib wt :
    (forall j t, @PCUICFirstorder.firstorder_type Σb #|ind_bodies mib| j t ->
      sfo_atom #|ind_bodies mib| j t) ->
    forallb (@PCUICFirstorder.firstorder_oneind Σb mib) (ind_bodies mib) ->
    mm_ok (init_mib_masks (Erasure.erase_ind rΣ wfrΣ kn mib wt)).
  Proof.
    intros hft hfo. apply erase_ind_mm_ok => oib c hin hc.
    destruct wt as [wt].
    have onb := onInductives wt.
    have ok : ar_ok (Erasure.arities_contexts kn (ind_bodies mib)).π1
      (Erasure.arities_contexts kn (ind_bodies mib)).π2 0
      #|ind_bodies mib|.
    { intros j _ hj.
      have hl : #|(Erasure.arities_contexts kn (ind_bodies mib)).π1| =
        #|ind_bodies mib|.
      { rewrite Erasure.arities_contexts_1. now len. }
      destruct (arities_contexts_inv kn (ind_bodies mib) j ltac:(lia))
        as [[ind hind] [decl [oib' [hn [hb [hty hin']]]]]].
      apply In_nth_error in hin' as [i' hi'].
      eapply Alli_nth_error in onb; tea.
      exists decl, (ind_params mib ,,, ind_indices oib'), (ind_sort oib'), ind.
      repeat split => //.
      - rewrite hty (ind_arity_eq onb) it_mkProd_or_LetIn_app //.
      - eapply forallb_forall in hfo; [|eapply nth_error_In; tea].
        move/andP: hfo => [_ hs]. destruct (ind_sort oib') => //. }
    apply In_nth_error in hin as [i hi].
    have oib_ok := Alli_nth_error _ _ _ _ _ _ onb hi.
    have hon := onConstructors oib_ok.
    apply In_nth_error in hc as [ci hci].
    destruct (All2_nth_error_Some _ _ hon hci) as [cu [_ oc]].
    eapply sfo_ty_fo_spine; [|exact ok].
    eapply (cstr_type_sfo Σb _ mib i oib); tea.
    - apply nth_error_Some_length in hi. lia.
    - eapply forallb_forall in hfo; [|eapply nth_error_In; tea].
      move/andP: hfo => [hcs _].
      eapply forallb_forall in hcs; [exact hcs|]. now eapply nth_error_In.
  Qed.
End TypedFO.

(** ** First-order environments *)

Lemma firstorder_env'_true decls nm :
  plookup_env (firstorder_env' decls) nm = Some true ->
  exists m, lookup_global decls nm = Some (InductiveDecl m) /\
    forallb (fun oib => negb (Sort.is_level (ind_sort oib))) (ind_bodies m).
Proof.
  induction decls as [|[kn' []] decls IH]; cbn => //.
  - destruct (eqb_spec nm kn') => //.
  - destruct (eqb_spec nm kn').
    + intros [= h]. subst. exists m. split => //.
      move: h. rewrite /firstorder_mutind. move/andP=> [_ h].
      eapply forallb_impl; tea. intros oib _.
      rewrite /firstorder_oneind. now move/andP=> [_ ?].
    + apply IH.
Qed.

Lemma fresh_lookup_global_In (decls : global_declarations) kn d :
  EnvMap.EnvMap.fresh_globals decls -> In (kn, d) decls ->
  lookup_global decls kn = Some d.
Proof.
  induction 1; cbn => //.
  intros [[= <- <-]|hin].
  - now rewrite eqb_refl.
  - destruct (eqb_spec kn kn0); [subst|now apply IHfresh_globals].
    apply EnvMap.EnvMap.fresh_global_iff_not_In in H0.
    elim H0. eapply in_map_iff. now exists (kn0, d).
Qed.

(** The first-order types of a declaration of [decls] are first-order in
    the sense of [sfo_atom], in any environment included in [decls]. *)
Lemma fo_type_sfo_atom (decls : global_declarations) rΣ' n j t :
  EnvMap.EnvMap.fresh_globals decls ->
  (forall x, In x (declarations rΣ'.1) -> In x decls) ->
  @firstorder_type (firstorder_env' decls) n j t -> sfo_atom rΣ' n j t.
Proof.
  intros fr hincl. rewrite /firstorder_type.
  destruct (decompose_app t) as [hd args] eqn:da. cbn.
  destruct hd => //; destruct args => //.
  - move/andP=> [/Nat.leb_le h1 /Nat.ltb_lt h2]. right.
    exists n0. split; [|lia].
    now rewrite (decompose_app_inv da).
  - destruct ind as [nm i].
    destruct plookup_env as [[]|] eqn:hl => // _.
    destruct (firstorder_env'_true _ _ hl) as [m [hm hs]].
    left. exists (mkInd nm i), ui.
    split; [now rewrite (decompose_app_inv da)|].
    intros mdecl idecl [hdecl hnth]. cbn in hdecl, hnth.
    rewrite (fresh_lookup_global_In _ _ _ fr (hincl _ hdecl)) in hm.
    noconf hm.
    eapply forallb_forall in hs; [|eapply nth_error_In; tea].
    destruct (ind_sort idecl) => //.
  - now destruct ind.
Qed.

(** ** The inductive types of the typed erased environment *)

Lemma erase_global_decl_not_ind {X_type : abstract_env_impl}
  {X : X_type.π2.π1} Σext hr kn cst wt mibx :
  @Erasure.erase_global_decl X_type X Σext hr kn (ConstantDecl cst) wt <>
  ExAst.InductiveDecl mibx.
Proof.
  unfold Erasure.erase_global_decl.
  destruct Erasure.erase_constant_decl; discriminate.
Qed.

Lemma erase_global_decl_ind {X_type : abstract_env_impl}
  {X : X_type.π2.π1} Σext hr kn mib wt :
  exists no' ni' wt',
    @Erasure.erase_global_decl X_type X Σext hr kn (InductiveDecl mib) wt =
    ExAst.InductiveDecl
      (@Erasure.erase_ind X_type X no' ni' Σext hr kn mib wt').
Proof.
  unfold Erasure.erase_global_decl. cbv beta iota.
  do 3 eexists. reflexivity.
Qed.

(** Every inductive type of the typed erased environment is the erasure of
    the PCUIC declaration of the same name, in the environment of the
    declarations that follow it. *)
Lemma erase_global_decls_deps_recursive_ind {X_type : abstract_env_impl}
  {X : X_type.π1} decls univs retro prop incl ign kn b mibx :
  In (kn, b, ExAst.InductiveDecl mibx)
    (@Erasure.erase_global_decls_deps_recursive X_type X decls univs retro
      prop incl ign) ->
  exists prefix tail mib, decls = prefix ++ (kn, InductiveDecl mib) :: tail /\
    exists (X' : X_type.π2.π1) no' ni' wfr wt,
      mibx = @Erasure.erase_ind X_type X' no' ni'
        (mk_global_env univs tail retro, ind_universes mib) wfr kn mib wt.
Proof.
  induction decls as [|[kn' d] decls IH] in X, prop, incl |- *.
  - cbn. easy.
  - cbn [Erasure.erase_global_decls_deps_recursive].
    destruct KernameSet.mem.
    + intros [e|hin].
      * injection e as -> _ e.
        destruct d as [cst|mib].
        { exfalso. exact (erase_global_decl_not_ind _ _ _ _ _ _ e). }
        match type of e with
        | @Erasure.erase_global_decl _ _ ?Σext ?hr _ _ ?wt = _ =>
          destruct (erase_global_decl_ind Σext hr kn mib wt)
            as [no' [ni' [wt' he]]]
        end.
        rewrite he in e. injection e as <-.
        exists [], decls, mib. split; [reflexivity|].
        do 2 eexists. exists ni'. do 2 eexists. reflexivity.
      * destruct (IH _ _ _ hin) as [prefix [tail [mib [-> h]]]].
        exists ((kn', d) :: prefix), tail, mib. split; [reflexivity|exact h].
    + intros hin.
      destruct (IH _ _ _ hin) as [prefix [tail [mib [-> h]]]].
      exists ((kn', d) :: prefix), tail, mib. split; [reflexivity|exact h].
Qed.

(** The initial dearging masks of the first-order inductive types of the
    typed erased environment remove nothing. *)
Lemma erase_global_decls_deps_recursive_mm_ok {X_type : abstract_env_impl}
  {X : X_type.π1} decls univs retro prop incl ign kn b mibx :
  EnvMap.EnvMap.fresh_globals decls ->
  In (kn, b, ExAst.InductiveDecl mibx)
    (@Erasure.erase_global_decls_deps_recursive X_type X decls univs retro
      prop incl ign) ->
  (exists m, lookup_global decls kn = Some (InductiveDecl m) /\
    @firstorder_mutind (firstorder_env' decls) m) ->
  mm_ok (init_mib_masks mibx).
Proof.
  intros fr hin [m [hm hfo]].
  destruct (erase_global_decls_deps_recursive_ind _ _ _ _ _ _ _ _ _ hin)
    as [prefix [tail [mib [-> [X' [no' [ni' [wfr [wt ->]]]]]]]]].
  rewrite (fresh_lookup_global_In _ kn (InductiveDecl mib) fr) in hm.
  { apply in_or_app. right. now left. }
  noconf hm.
  move: hfo. rewrite /firstorder_mutind. move/andP=> [_ hfo].
  eapply (erase_ind_fo_mm_ok _ wfr (firstorder_env' (prefix ++ _)));
    [|exact hfo].
  intros j t. apply fo_type_sfo_atom; [exact fr|].
  intros x hx. apply in_or_app. right. now right.
Qed.
