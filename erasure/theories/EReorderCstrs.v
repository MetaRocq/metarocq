From Stdlib Require Import List String Arith Lia ssreflect ssrbool Morphisms.
Import ListNotations.
From Equations Require Import Equations.
Set Equations Transparent.

From MetaRocq.PCUIC Require Import PCUICAstUtils.
From MetaRocq.Utils Require Import MRList bytestring utils monad_utils.
From MetaRocq.Erasure Require Import EProgram EPrimitive EAst ESpineView EEtaExpanded EInduction ERemoveParams Erasure EGlobalEnv
  EAstUtils ELiftSubst EWellformed ECSubst EWcbvEval.

Import Kernames.
Import MRMonadNotation.

Lemma lookup_declared_constructor {Σ id mdecl idecl cdecl} :
  lookup_constructor Σ id.1 id.2 = Some (mdecl, idecl, cdecl) ->
  declared_constructor Σ id mdecl idecl cdecl.
Proof.
  rewrite /lookup_constructor /declared_constructor.
  rewrite /declared_inductive /lookup_inductive.
  rewrite /declared_minductive /lookup_minductive.
  destruct lookup_env => //=. destruct g => //=.
  destruct nth_error eqn:hn => //. destruct (nth_error _ id.2) eqn:hn' => //.
  intros [= <- <- <-]. intuition auto.
Qed.

Fixpoint lookup_inductive_assoc {A} (Σ : list (inductive × A)) (kn : inductive) {struct Σ} : option A :=
    match Σ with
    | [] => None
    | d :: tl => if kn == d.1 then Some d.2 else lookup_inductive_assoc tl kn
    end.

Section Tags.

  Fixpoint find_tag (l : list nat) (idx : nat) (tag : nat) : option nat :=
    match l with
    | [] => None
    | tag' :: tags => if tag == tag' then Some idx
      else find_tag tags (S idx) tag
    end.
  (* e.g. for bool: [ 1 0 ], i.e true (0 in Rocq) is mapped to 1 and false (1 in Rocq) is mapped to 0 *)
  Definition new_tag tags tag := find_tag tags 0 tag.
  Definition old_tag (tags : list nat) tag := nth_error tags tag.

  Lemma new_tag_spec tags newidx oldidx :
    new_tag tags newidx = Some oldidx ->
    old_tag tags oldidx = Some newidx.
  Proof.
    rewrite /old_tag /new_tag.
    rewrite -{2}[oldidx]Nat.sub_0_r. generalize 0.
    induction tags in oldidx |- *.
    - intros n0. now rewrite nth_error_nil.
    - cbn. intros n0. case: eqb_spec.
      * move=> -> [= ->]. now rewrite Nat.sub_diag.
      * intros neq h. specialize (IHtags _ _ h).
        case H: (oldidx - n0) => [|n].
        + cbn. assert (oldidx - S n0 = 0). lia. rewrite H0 in IHtags.
          destruct tags; cbn in * => //.
          noconf IHtags. rewrite eqb_refl in h. noconf h. lia.
        + cbn. destruct oldidx; try lia. rewrite Nat.sub_succ in IHtags.
          assert (oldidx - n0 = n) by lia. now rewrite H0 in IHtags.
  Qed.

  Definition reorder_list_opt {A} tags (brs : list A) : option (list A) :=
    mapopt (nth_error brs) tags.

  Definition reorder_list {A} tags (l : list A) :=
    option_get l (reorder_list_opt tags l).

  Fixpoint one_to_one_map n l :=
      match n with
      | 0 => l == nil
      | S n =>
        existsb (fun x => x == n) l && one_to_one_map n (remove Nat.eq_dec n l)
      end.

  Definition wf_tags (l : list nat) :=
    forallb (fun n => n <? #|l|) l && one_to_one_map #|l| l.

  Lemma find_tag_None tags n idx :
    find_tag tags n idx = None ->
    Forall (fun tag => tag <> idx) tags.
  Proof.
    induction tags in n |- *; cbn; auto.
    case: eqb_spec => [->|neq] // h.
    specialize (IHtags _ h). constructor; auto.
  Qed.

  Lemma one_to_one_map_spec l : one_to_one_map #|l| l ->
    forall i, i < #|l| <-> In i l.
  Proof.
    move: (Nat.le_refl #|l|).
    generalize #|l| at 2 3 4 as n. induction n in l |- *; cbn.
    - move=> hl _ i; split => //. lia. move: l hl; case => //=; try lia.
    - move=> hl /andP[] /existsb_exists => [[x [inx xeqn]]] hone i.
      specialize (IHn (remove Nat.eq_dec n l)).
      apply eqb_eq in xeqn. subst x.
      forward IHn.
      have hlt := remove_length_lt Nat.eq_dec l n inx. lia.
      specialize (IHn hone).
      case: (eqb_spec i n) => [->|neq]. intuition auto.
      split => hi. assert (i < n) by lia.
      now have := proj1 (IHn _) H => /(in_remove Nat.eq_dec).
      suff: i < n by lia. apply <- IHn.
      apply (in_in_remove Nat.eq_dec) => //.
  Qed.

  Lemma find_tag_wf tags idx :
    wf_tags tags ->
    new_tag tags idx = None ->
    #|tags| <= idx.
  Proof.
    rewrite /wf_tags => /andP[] /forallb_All hwf.
    move => /one_to_one_map_spec hone /find_tag_None /Forall_forall hdiff.
    case: (Nat.leb_spec #|tags| idx) => // hlt.
    elim (hdiff idx). apply hone, hlt. reflexivity.
  Qed.

  Lemma mapopt_spec {A B} (f : A -> option B) (l : list A) :
    (forall i x, nth_error l i = Some x -> exists x', f x = Some x') ->
    exists l', mapopt f l = Some l' /\
    (forall i x, nth_error l i = Some x -> exists x', f x = Some x' /\ nth_error l' i = f x).
  Proof.
    induction l; cbn.
    - intros hf. exists []. split => // i x. rewrite nth_error_nil //.
    - intros hf. forward IHl.
      { intros i x hx. apply (hf (S i) x hx). }
      destruct IHl as [l' [exl' hl']].
      specialize (hf 0 a eq_refl) as [x' eqx'].
      destruct (f a) eqn:fa.
      * noconf eqx'. rewrite exl'.
        eexists; split => //.
        intros i x hnth. destruct i; cbn in *. now noconf hnth.
        now apply hl'.
      * discriminate.
  Qed.

  Lemma mapopt_inv_spec {B} (f : nat -> option B) (l : list nat) :
    (forall i x, nth_error l i = Some x -> exists x', f x = Some x') ->
    exists l', mapopt f l = Some l' /\ #|l| = #|l'| /\
    (forall i x, nth_error l' i = Some x -> exists x', nth_error l i = Some x' /\ f x' = Some x).
  Proof.
    induction l; cbn.
    - intros hf. exists []. split => //; split => // i x. rewrite nth_error_nil //.
    - intros hf. forward IHl.
      { intros i x hx. apply (hf (S i) x hx). }
      destruct IHl as [l' [exl' hl']].
      specialize (hf 0 a eq_refl) as [x' eqx'].
      rewrite eqx' exl'. eexists; split => //= //. split => //. lia.
      intros.
      destruct hl' as [hl hl']. destruct i. cbn in *. noconf H. exists a. now split => //.
      now apply hl'.
  Qed.

  (*Lemma mapopt_spec' {B} (f : nat -> option B) (l : list nat) :
    (forall i x, nth_error l i = Some x -> exists x', f x = Some x') ->
    exists l', mapopt f l = Some l' /\
    (forall i x, nth_error l i = Some x -> exists b, f x = Some b /\ nth_error l' x = Some b).
  Proof.
    induction l; cbn.
    - intros hf. exists []. split => // i x. rewrite nth_error_nil //.
    - intros hf. forward IHl.
      { intros i x hx. apply (hf (S i) x hx). }
      destruct IHl as [l' [exl' hl']].
      pose proof (hf 0 a eq_refl) as [x' eqx'].
      destruct (f a) eqn:fa => //.
      noconf eqx'. rewrite exl'.
      eexists; split => //.
      intros i x hnth. destruct i; cbn in *. noconf hnth.
      * exists x'. split => //. destruct a; cbn. congruence.
        apply hl'.
      * discriminate.
  Qed. *)

  Lemma reorder_list_opt_spec {A} (l : list A) (tags : list nat) (htags : wf_tags tags) :
    #|l| = #|tags| ->
    exists l', reorder_list_opt tags l = Some l' /\
    (forall i k, old_tag tags i = Some k -> exists x, nth_error l k = Some x /\ nth_error l' i = nth_error l k).
  Proof.
    rewrite /reorder_list_opt.
    rewrite /wf_tags in htags.
    intros hlen.
    move/andP: htags => [] htags _.
    have optH := mapopt_spec (nth_error l) tags.
    forward optH.
    { intros i x hnth. solve_all. eapply All_nth_error in htags; tea. apply Nat.ltb_lt in htags.
      rewrite -hlen in htags.
      apply nth_error_Some in htags. destruct (nth_error l x) eqn:hnth'; try congruence. now eexists. }
    destruct optH as [l' [heq hl']].
    setoid_rewrite heq. eexists; split => //.
  Qed.

  Lemma reorder_list_opt_In {A} (l : list A) (tags : list nat) l' :
    reorder_list_opt tags l = Some l' ->
    (forall x, In x l' -> In x l).
  Proof.
    rewrite /reorder_list_opt.
    induction tags in l, l' |- *; cbn.
    - intros [= <-] x [].
    - destruct nth_error eqn:hnth => //.
      destruct mapopt eqn:hmap => //.
      intros [= <-] x [->|].
      now eapply nth_error_In in hnth.
      eapply IHtags; tea.
  Qed.

  (* Lemma reorder_list_spec {A} (tags : list nat) (l : list A) n i :
    wf_tags tags -> #|l| = #|tags| ->
    nth_error tags i = Some n ->
    nth_error (reorder_list tags l) i = nth_error l n.
  Proof.
    intros wft hlt hnth.
    rewrite /reorder_list.
    now have [l' [-> hnth']] := reorder_list_opt_spec l tags wft hlt.
  Qed. *)

  (* Definition reorder_list_spec_maps {A} (l : list A) (tags : list nat) :
    forall l', reorder_list_opt tags l = Some l' ->
      (forall i k, maps_to tags i k -> nth_error l' k = nth_error l i).
  Proof.
    intros l'.
    induction l; cbn.
    - destruct l'; cbn.
      intros [=] i k. now rewrite !nth_error_nil.
      rewrite /reorder_list_opt /=.
      destruct tags => //=. now rewrite nth_error_nil.
    - rewrite /reorder_list_opt. *)

  Definition inj_tags (tags : list nat) :=
    forall i i' k, nth_error tags i = Some k -> nth_error tags i' = Some k -> i = i'.

  Lemma reorder_list_opt_spec' {A} (l : list A) (tags : list nat) (htags : wf_tags tags) :
    #|l| = #|tags| ->
    (* inj_tags tags -> *)
    exists l', reorder_list_opt tags l = Some l' /\
    (forall oldidx a, nth_error l' oldidx = Some a ->
      exists newidx, old_tag tags oldidx = Some newidx /\ nth_error l newidx = Some a).
  Proof.
    rewrite /reorder_list_opt.
    rewrite /wf_tags in htags.
    move: htags => /andP[] htags hone.
    intros hlen.
    have optH := mapopt_inv_spec (nth_error l) tags.
    forward optH.
    { intros i x hnth. solve_all. eapply All_nth_error in htags; tea. apply Nat.ltb_lt in htags.
      rewrite -hlen in htags.
      apply nth_error_Some in htags. destruct (nth_error l x) eqn:hnth'; try congruence. now eexists. }
    destruct optH as [l' [heq hl']].
    setoid_rewrite heq. eexists; split => //.
    destruct hl' as [hlen' hl'].
    intros newidx a hnth.
    specialize (hl' _ _ hnth).
    destruct hl' as [x' [eqx' hl']]. exists x'. split => //.
  Qed.

  Lemma reorder_list_spec' {A} (tags : list nat) (l : list A) n i x :
    wf_tags tags -> #|l| = #|tags| ->
    nth_error tags i = Some n -> (* tags[0] = 1 *)
    nth_error l n = Some x -> (* l[1] = info *)
    nth_error (reorder_list tags l) i = Some x. (* l'[0] = info*)
  Proof.
    intros wft hlt hnth hnth'.
    rewrite /reorder_list.
    have [l' [-> hnth'']] := reorder_list_opt_spec l tags wft hlt.
    cbn. specialize (hnth'' _ _ hnth). destruct hnth'' as [? []]. congruence.
  Qed.

  Lemma reorder_list_spec_inv {A} (tags : list nat) (l : list A) n x :
    wf_tags tags -> #|l| = #|tags| ->
    nth_error (reorder_list tags l) n = Some x -> (* n is a new index, i an old one *)
    exists i, nth_error tags n = Some i /\ nth_error l i = Some x.
  Proof.
    intros wft hlt.
    rewrite /reorder_list.
    have [l' [eq hnth'']] := reorder_list_opt_spec' l tags wft hlt; rewrite eq /= => hnth.
    specialize (hnth'' _ _ hnth) as [oldidx []]. exists oldidx; now split.
  Qed.


  Lemma reorder_list_old_tag {A} (tags : list nat) (l : list A) oldidx newidx :
    wf_tags tags -> #|l| = #|tags| ->
    old_tag tags newidx = Some oldidx ->
    nth_error (reorder_list tags l) newidx = nth_error l oldidx.
  Proof.
    rewrite /old_tag.
    intros wft hlen ht.
    destruct (nth_error l) eqn:hl => //=.
    eapply (reorder_list_spec' tags l) in ht; tea.
    move: wft => /andP[] wft hone.
    solve_all. eapply All_nth_error in wft; tea.
    apply Nat.ltb_lt in wft. rewrite -hlen in wft. apply nth_error_None in hl. lia.
  Qed.

(* Lemma reorder_list_old_tag' {A} (tags : list nat) (l : list A) oldidx newidx :
    wf_tags tags -> #|l| = #|tags| ->
    old_tag tags oldidx = Some newidx ->
    nth_error (reorder_list tags l) oldidx = nth_error l newidx.
  Proof.
    rewrite /old_tag.
    intros wft hlen ht.
    destruct (nth_error l) eqn:hl => //=.
    eapply (reorder_list_spec' tags l) in ht; tea.
    move/andP: wft => [] wft hone.
    unfold wf_tags in wft. solve_all. eapply All_nth_error in wft; tea.
    apply Nat.ltb_lt in wft. rewrite -hlen in wft. apply nth_error_None in hl. lia.
  Qed.
*)

  (* Lemma reorder_list_old_tag_inv {A} (tags : list nat) (l : list A) oldidx newidx :
    wf_tags tags -> #|l| = #|tags| ->
    old_tag tags oldidx = Some newidx ->
    nth_error (reorder_list tags l) newidx = nth_error l oldidx.
  Proof.
    rewrite /old_tag.
    intros wft hlen ht.
    destruct (nth_error l) eqn:hl => //=.
    eapply (reorder_list_spec tags l) in ht; tea.
    unfold wf_tags in wft. solve_all. eapply All_nth_error in wft; tea.
    apply Nat.ltb_lt in wft. rewrite -hlen in wft. apply nth_error_None in hl. lia.
  Qed. *)


End Tags.

Section Reorder.
  Context (Σ : global_declarations).
  Context (mapping : inductives_mapping).

  Definition lookup_constructor_mapping i c :=
    '(tyna, tags) <- lookup_inductive_assoc mapping i ;;
    new_tag tags c.

  Definition lookup_constructor_ordinal i c :=
    match lookup_constructor_mapping i c with
    | None => c
    | Some c' => c'
    end.

  Definition reorder_branches (i : inductive) (brs : list (list BasicAst.name × term)) : list (list BasicAst.name × term) :=
    match lookup_inductive_assoc mapping i with
    | None => brs
    | Some (tyna, tags) => reorder_list tags brs
    end.

  Equations reorder (t : term) : term :=
    | tVar na => tVar na
    | tLambda nm bod => tLambda nm (reorder bod)
    | tLetIn nm dfn bod => tLetIn nm (reorder dfn) (reorder bod)
    | tApp fn arg => tApp (reorder fn) (reorder arg)
    | tConst nm => tConst nm
    | tConstruct i m args => tConstruct i (lookup_constructor_ordinal i m) (map reorder args)
    | tCase i mch brs => tCase i (reorder mch) (reorder_branches i.1 (map (on_snd reorder) brs))
    | tFix mfix idx => tFix (map (map_def reorder) mfix) idx
    | tCoFix mfix idx => tCoFix (map (map_def reorder) mfix) idx
    | tProj p bod =>
      tProj p (reorder bod)
    | tPrim p => tPrim (map_prim reorder p)
    | tLazy t => tLazy (reorder t)
    | tForce t => tForce (reorder t)
    | tRel n => tRel n
    | tBox => tBox
    | tEvar ev args => tEvar ev (map reorder args).

    Definition reorder_constant_decl cb :=
      {| cst_body := option_map reorder cb.(cst_body) |}.

    Definition reorder_one_ind kn i (oib : one_inductive_body) : one_inductive_body :=
      match lookup_inductive_assoc mapping {| inductive_mind := kn; inductive_ind := i |} with
      | None => oib
      | Some (tyna, tags) =>
        {| ind_name := oib.(ind_name);
           ind_propositional := oib.(ind_propositional);
           ind_kelim := oib.(ind_kelim);
           ind_ctors := reorder_list tags oib.(ind_ctors);
           ind_projs := oib.(ind_projs) |}
      end.

    Definition reorder_inductive_decl kn idecl :=
      {| ind_finite := idecl.(ind_finite); ind_npars := idecl.(ind_npars);
         ind_bodies := mapi (reorder_one_ind kn) idecl.(ind_bodies) |}.

    Definition reorder_decl d :=
      let d' := match d.2 with
      | ConstantDecl cb => ConstantDecl (reorder_constant_decl cb)
      | InductiveDecl idecl => InductiveDecl (reorder_inductive_decl d.1 idecl)
      end in
      (d.1, d').

    Definition reorder_env Σ :=
      map (reorder_decl) Σ.

End Reorder.

Definition reorder_program mapping (p : program) : program :=
  (reorder_env mapping p.1, reorder mapping p.2).

Definition wf_tags_list (tags : list nat) (n : nat) :=
  (#|tags| == n) && wf_tags tags.

Lemma nth_error_reorder {A} {l : list A} {tags n newidx} :
  wf_tags_list tags #|l| ->
  old_tag tags newidx = Some n ->
  nth_error (reorder_list tags l) newidx = nth_error l n.
Proof.
  move=> /andP [] h. apply eqb_eq in h. move=> wft hnw.
  pose proof (reorder_list_old_tag tags l n newidx wft).
  now apply H.
Qed.

Definition wf_reordering ncstrs cstrs :=
  (List.length cstrs == ncstrs) &&
  one_to_one_map ncstrs cstrs.

Definition wf_inductive_mapping (Σ : global_declarations) (m : inductive_mapping) : bool :=
  let '(ind, (_, cstrs)) := m in
  match EGlobalEnv.lookup_inductive Σ ind with
  | Some (mib, oib) => wf_tags_list cstrs #|oib.(ind_ctors)|
  | None => true
  end.

Definition wf_inductives_mapping Σ (m : inductives_mapping) : bool :=
  forallb (wf_inductive_mapping Σ) m.

Section reorder_proofs.
  Context (Σ : global_declarations) (m : inductives_mapping).
  Context (wfm : wf_inductives_mapping Σ m).

  Notation optimize := (reorder m).

  Lemma optimize_mkApps f l : optimize (mkApps f l) = mkApps (optimize f) (map optimize l).
  Proof using Type.
    induction l using rev_ind; simpl; auto.
    now rewrite mkApps_app /= IHl map_app /= mkApps_app /=.
  Qed.

  Lemma map_optimize_repeat_box n : map optimize (repeat tBox n) = repeat tBox n.
  Proof using Type. by rewrite map_repeat. Qed.

  (* move to globalenv *)

  Lemma isLambda_optimize t : isLambda t -> isLambda (optimize t).
  Proof. destruct t => //. Qed.
  Lemma isBox_optimize t : isBox t -> isBox (optimize t).
  Proof. destruct t => //. Qed.

  Lemma lookup_env_reorder kn : lookup_env (reorder_env m Σ) kn = option_map (fun decl => snd (reorder_decl m (kn, decl))) (lookup_env Σ kn).
  Proof.
    clear wfm. induction Σ; cbn; auto.
    case: eqb_spec => [->|hneq] //=.
  Qed.

  Lemma lookup_constant_reorder c : option_map (reorder_constant_decl m) (lookup_constant Σ c) = lookup_constant (reorder_env m Σ) c.
  Proof.
    rewrite /lookup_constant lookup_env_reorder.
    destruct lookup_env => //=.
    destruct g => //.
  Qed.

  Lemma lookup_inductive_reorder i :
    lookup_inductive (reorder_env m Σ) i = option_map (fun '(mib, oib) =>
      (reorder_inductive_decl m i.(inductive_mind) mib, reorder_one_ind m i.(inductive_mind) i.(inductive_ind) oib))
       (lookup_inductive Σ i).
  Proof.
    unfold lookup_inductive, lookup_minductive.
    unfold reorder_env. rewrite lookup_env_reorder.
    destruct lookup_env => //=.
    destruct g => //.
    cbn. rewrite nth_error_mapi.
    destruct nth_error => //=.
  Qed.

  Lemma lookup_inductive_assoc_spec {ind p} :
    wf_inductives_mapping Σ m ->
    lookup_inductive_assoc m ind = Some p ->
    wf_inductive_mapping Σ (ind, p).
  Proof.
    clear. rewrite /wf_inductives_mapping.
    induction m; cbn -[lookup_inductive wf_inductive_mapping] => //.
    destruct eq_inductive eqn:heq => //.
    - move=> /andP[] wfa wfi. intros [= <-].
      apply eqb_eq in heq. subst ind. destruct a; apply wfa.
    - move=> /andP[] wfa wfi. intros hl. now apply IHi.
  Qed.

  Lemma lookup_inductive_assoc_wf_tags {ind mib oib p} :
    lookup_inductive Σ ind = Some (mib, oib) ->
    lookup_inductive_assoc m ind = Some p ->
    wf_tags_list (snd p) #|oib.(ind_ctors)|.
  Proof.
    move=> hl.
    move/(lookup_inductive_assoc_spec wfm).
    rewrite /wf_inductive_mapping hl.
    now destruct p.
  Qed.

  Lemma ind_ctors_reorder {ind mib oib p} :
    lookup_inductive Σ ind = Some (mib, oib) ->
    lookup_inductive_assoc m ind = Some p ->
    ind_ctors (reorder_one_ind m ind.(inductive_mind) ind.(inductive_ind) oib) =
    reorder_list p.2 (ind_ctors oib).
  Proof.
    intros hli hia.
    unfold reorder_one_ind.
    destruct ind; rewrite hia. destruct p. now cbn.
  Qed.

  Lemma ind_ctors_no_reorder {ind mib oib} :
    lookup_inductive Σ ind = Some (mib, oib) ->
    lookup_inductive_assoc m ind = None ->
    ind_ctors (reorder_one_ind m ind.(inductive_mind) ind.(inductive_ind) oib) =
    ind_ctors oib.
  Proof.
    intros hli hia.
    unfold reorder_one_ind.
    now destruct ind; rewrite hia.
  Qed.

  Lemma nth_reorder_list_ctors {i mib oib na tags} :
    lookup_inductive Σ i = Some (mib, oib) ->
    lookup_inductive_assoc m i = Some (na, tags) ->
    forall newidx n, old_tag tags newidx = Some n ->
    nth_error (reorder_list tags oib.(ind_ctors)) newidx = nth_error oib.(ind_ctors) n.
  Proof.
    move=> hli hia idx hnew.
    apply nth_error_reorder => //.
    eapply (lookup_inductive_assoc_wf_tags (p:=(na, tags))); tea.
  Qed.

  Lemma map_opt_length {A B} (f : A -> option B) l :
    match mapopt f l with
    | None => True
    | Some l' => #|l'| = #|l|
    end.
  Proof.
    induction l; cbn; auto.
    destruct (f a) => //.
    destruct (mapopt f l) => //=. now f_equal.
  Qed.

  Lemma reorder_list_length {A} tags (l : list A): #|tags| = #|l| -> #|reorder_list tags l| = #|l|.
  Proof.
    move=> hl. rewrite /reorder_list.
    case hr: reorder_list_opt => [l'|] //=.
    move: hr; rewrite /reorder_list_opt.
    have := map_opt_length (nth_error l) tags.
    destruct mapopt => //. congruence.
  Qed.

  Lemma lookup_inductive_assoc_None_reorder_one_ind i oib :
    lookup_inductive_assoc m i = None ->
    reorder_one_ind m (inductive_mind i) (inductive_ind i) oib = oib.
  Proof.
    rewrite /reorder_one_ind. destruct i; move => -> //.
  Qed.
(*
  Lemma lookup_inductive_assoc_None_reorder_inductive_decl i mib :
    lookup_inductive_assoc m i = None ->
    reorder_inductive_decl m (inductive_mind i) mib = mib.
  Proof.
    rewrite /reorder_inductive_decl.
    intros hl. destruct mib; f_equal.
    cbn; induction ind_bodies => //=. f_equal; eauto.
    rewrite (lookup_inductive_assoc_None_reorder_one_ind {| inductive_mind := inductive_mind i; inductive_ind := 0 |}). //.

  Qed. *)
  Arguments eqb_eq {A H x y}.
  Lemma lookup_constructor_reorder i n :
    option_map (fun '(mib, oib, c) => (reorder_inductive_decl m (inductive_mind i) mib, reorder_one_ind m (inductive_mind i) (inductive_ind i) oib, c)) (lookup_constructor Σ i n) =
    lookup_constructor (reorder_env m Σ) i (lookup_constructor_ordinal m i n).
  Proof using Type wfm.
    rewrite /lookup_constructor lookup_inductive_reorder.
    destruct lookup_inductive as [[mib oib]|] eqn:hind => //=.
    destruct nth_error eqn:hnth => //=.
    destruct (lookup_inductive_assoc m i) as [(na, tags)|] eqn:hl.
    have /andP[]  := lookup_inductive_assoc_wf_tags hind hl => //= /eqb_eq => hlen wft.
    rewrite (ind_ctors_reorder hind hl). cbn.
    destruct (nth_error _ (lookup_constructor_ordinal _ _ _)) eqn:hnth'.
    rewrite /lookup_constructor_ordinal /lookup_constructor_mapping in hnth'.
    rewrite hl /= in hnth'.
    destruct (new_tag tags n) as [newidx|] eqn:ht.
    - eapply new_tag_spec in ht.
      now rewrite (nth_reorder_list_ctors hind hl _ n) in hnth'.
    - move/nth_error_Some_length: hnth.
      rewrite /new_tag in ht => hn.
      eapply find_tag_wf in ht => //. lia.
    - eapply nth_error_None in hnth'.
      apply nth_error_Some_length in hnth.
      rewrite reorder_list_length in hnth' => //.
      move: hnth'.
      rewrite /lookup_constructor_ordinal /lookup_constructor_mapping hl /=.
      destruct (new_tag tags n) as [newidx|] eqn:ht.
      eapply new_tag_spec in ht.
      apply nth_error_Some_length in ht. lia.
      rewrite /new_tag in ht => hn.
      eapply find_tag_wf in ht => //. lia.
    - rewrite /lookup_constructor_ordinal /lookup_constructor_mapping hl //=.
      destruct i.
      rewrite /reorder_one_ind hl //=. now rewrite hnth.
    - apply nth_error_None in hnth.
      rewrite /lookup_constructor_ordinal /lookup_constructor_mapping /=.
      destruct lookup_inductive_assoc eqn:hl => //=.
      have /andP[]  := lookup_inductive_assoc_wf_tags hind hl => //= /(eqb_eq (A:=nat)) => hlen wft.
      destruct p as [na tags].
      destruct (new_tag tags n) as [newidx|] eqn:ht.
      + eapply new_tag_spec in ht.
        move/andP: wft => [] ht' _.
        eapply forallb_All in ht'. eapply All_nth_error in ht'; tea. apply Nat.ltb_lt in ht'. lia.
      + rewrite /reorder_one_ind. destruct i; rewrite hl //=.
        destruct nth_error eqn:hnth' => //.
        apply nth_error_Some_length in hnth'. rewrite reorder_list_length in hnth'. cbn in hlen; lia. lia.
      + rewrite lookup_inductive_assoc_None_reorder_one_ind //=.
        destruct nth_error eqn:hnth' => //.
        apply nth_error_Some_length in hnth'. lia.
  Qed.

  Lemma ind_projs_reorder mind ind oib :
    ind_projs (reorder_one_ind m mind ind oib) = ind_projs oib.
  Proof.
    rewrite /reorder_one_ind. destruct lookup_inductive_assoc as [[na tags]|]=> //.
  Qed.

  Context {efl : EEnvFlags}.
  Context {wca : cstr_as_blocks = false}.

  Lemma wf_glob_ind_projs {p pinfo} :
    wf_glob Σ ->
    lookup_projection Σ p = Some pinfo ->
    #|(ind_ctors pinfo.1.1.2)| = 1.
  Proof.
    intros wf.
    rewrite /lookup_projection /lookup_constructor /lookup_inductive /lookup_minductive.
    destruct lookup_env eqn:hl => //.
    have := lookup_env_wellformed wf hl.
    destruct g as [|mib] => //=.
    destruct nth_error eqn:hind => //=.
    destruct ind_ctors eqn:hctors => //=.
    destruct (nth_error (ind_projs o) _) eqn:hprojs => //=.
    intros wfmind [= <-]. cbn.
    move: wfmind; rewrite /wf_minductive.
    move/andP=> [] _ /forallb_All ha.
    eapply All_nth_error in ha; tea.
    move: ha; rewrite /wf_inductive /wf_projections.
    destruct ind_projs => //. now rewrite nth_error_nil in hprojs.
    rewrite hctors. destruct l => //.
  Qed.


  Lemma lookup_projection_ordinal p :
    wf_glob Σ ->
    isSome (lookup_projection Σ p) ->
    lookup_constructor_ordinal m (proj_ind p) 0 = 0.
  Proof.
    move=> wf.
    case hl: lookup_projection => [pro|] //= _.
    have wfpro := wf_glob_ind_projs wf hl. move: hl.
    rewrite /lookup_projection /lookup_constructor_ordinal.
    destruct lookup_constructor as [[[mib oib] cb]|] eqn:hlc => //=.
    destruct nth_error eqn:nthp => //=. intros [= <-]. cbn in wfpro.
    rewrite /lookup_constructor_mapping.
    destruct lookup_inductive_assoc as [[na tags]|] eqn:hla => //=.
    destruct new_tag eqn:hnt => //=.
    eapply new_tag_spec in hnt.
    eapply lookup_inductive_assoc_spec in hla; tea.
    rewrite /wf_inductive_mapping in hla.
    eapply lookup_constructor_lookup_inductive in hlc. rewrite hlc in hla.
    move/andP: hla. rewrite wfpro. rewrite /wf_tags => [] [] taglen /andP[] /forallb_All ht.
    destruct tags as [|] => //. destruct tags as [|] => //.
    destruct n => //. cbn in hnt. now rewrite nth_error_nil in hnt.
  Qed.

  Lemma lookup_projection_reorder p :
    wf_glob Σ ->
    isSome (lookup_projection Σ p) ->
    lookup_projection (reorder_env m Σ) p = option_map (fun '(((mib, oib), c), pb) =>
      (reorder_inductive_decl m p.(proj_ind).(inductive_mind) mib,
        reorder_one_ind m p.(proj_ind).(inductive_mind) p.(proj_ind).(inductive_ind) oib,
        c, pb))
       (lookup_projection Σ p).
  Proof.
    intros wf iss. unfold lookup_projection.
    rewrite -{1}(lookup_projection_ordinal _ wf iss) -lookup_constructor_reorder.
    destruct lookup_constructor eqn:hlc => //=.
    destruct p0 as [[mib oib] cb] => //=.
    rewrite ind_projs_reorder //=.
    destruct nth_error eqn:nthp => //=.
  Qed.

  Lemma All_reorder_list {A tags} {P : A -> Prop} {l} :
    All P l ->
    All P (reorder_list tags l).
  Proof.
    rewrite /reorder_list.
    destruct reorder_list_opt as [l'|] eqn:hre => //=.
    have hin := reorder_list_opt_In _ _ _ hre.
    move/(All_Forall).
    move/(Forall_forall _ _) => hl.
    apply Forall_All, Forall_forall. intuition eauto.
  Qed.

  Lemma wf_ind_mapping_wf_brs {ind n nas tags} : wf_brs Σ ind n ->
    lookup_inductive_assoc m ind = Some (nas, tags) ->
    #|tags| = n.
  Proof.
    rewrite /wf_brs.
    destruct lookup_inductive as [[mib oib]|] eqn:hli => //.
    move=> /eqb_eq hlen hla.
    have := lookup_inductive_assoc_wf_tags hli hla.
    rewrite /wf_tags_list /= => /andP[] /eqb_eq hlt _. lia.
  Qed.

  Ltac rtoProp ::=
  repeat match goal with
  | H : is_true (_ && _) |- _ => apply andb_and in H; destruct H
  | |- context [is_true (_ && _)] => rewrite andb_and
  | H : is_true (_ || _) |- _ => move/orP: H => H; destruct H
  | |- context [is_true (_ || _)] => apply/orP
  end.



  Lemma wf_optimize t k :
    wf_glob Σ ->
    wellformed Σ k t -> wellformed (reorder_env m Σ) k (optimize t).
  Proof using Type wfm wca.
    intros wfΣ.
    induction t in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold wf_fix_gen, test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; bool; solve_all]; try easy.
    - bool. rewrite -lookup_constant_reorder. destruct lookup_constant => //=; bool.
      now destruct (cst_body c) => //=.
    - rewrite wca in H *. move/andP: H => [] /andP[] -> iss isnil /=.
      rewrite -lookup_constructor_reorder.
      destruct lookup_constructor eqn:hl => //=.
      destruct args => //.
    - rtoProp; intuition auto; solve_all.
      * rewrite /reorder_branches.
        destruct lookup_inductive_assoc as [[na tags]|] eqn:hl => //=.
        have lenreo := wf_ind_mapping_wf_brs H0 hl.
        rewrite reorder_list_length. len. len.
        move: H0. rewrite /wf_brs. destruct p as [[mind ind] i].
        rewrite lookup_inductive_reorder. destruct lookup_inductive as [[mib oib]|]=> //=.
        rewrite /reorder_one_ind hl /=. move/eqb_eq => hl'. rewrite reorder_list_length //. lia.
        now apply Nat.eqb_eq. len.
        move: H0. rewrite /wf_brs. destruct p as [[mind ind] i].
        rewrite lookup_inductive_reorder. destruct lookup_inductive as [[mib oib]|]=> //=.
        rewrite /reorder_one_ind hl /=. move/eqb_eq => hl'. now apply Nat.eqb_eq.
      * rewrite /reorder_branches.
        destruct lookup_inductive_assoc as [[nas tags]|].
        eapply All_reorder_list.
        all:solve_all.
    - rtoProp; intuition auto.
      rewrite lookup_projection_reorder //.
      destruct lookup_projection => //.
    - rtoProp; intuition auto; solve_all.
      destruct (dbody x) => //.
    - rtoProp; intuition auto; solve_all.
      depelim H1; constructor; eauto. intuition auto.
      cbn; solve_all.
  Qed.

  Instance mapopt_ext {A B} :
    Proper (pointwise_relation A eq ==> eq ==> eq) (@mapopt A B).
  Proof.
    intros f g eqfg l ? <-.
    induction l; cbn; auto.
    rewrite (eqfg a). destruct (g a) => //.
    now rewrite IHl.
  Qed.

  Lemma mapopt_option_map {A B C} (f : A -> option B) (g : B -> C) l :
    mapopt (fun x => option_map g (f x)) l = option_map (map g) (mapopt f l).
  Proof.
    induction l; cbn; auto.
    destruct (f a) => //=.
    rewrite IHl. destruct (mapopt f l) => //.
  Qed.

  Lemma reorder_list_opt_map {A B} tags (f : A -> B) (l : list A) :
    reorder_list_opt tags (map f l) = option_map (map f) (reorder_list_opt tags l).
  Proof.
    rewrite /reorder_list_opt.
    have req : pointwise_relation nat eq (nth_error (map f l)) (fun x => option_map f (nth_error l x)).
    { intros x. now rewrite nth_error_map. }
    setoid_rewrite req. now rewrite mapopt_option_map.
  Qed.

  Lemma reorder_branches_map i f brs :
    reorder_branches m i (map f brs) =
    map f (reorder_branches m i brs).
  Proof.
    rewrite /reorder_branches.
    destruct lookup_inductive_assoc as [[na tags]|] eqn:hl => //.
    rewrite /reorder_list.
    rewrite reorder_list_opt_map.
    destruct (reorder_list_opt tags brs) => //=.
  Qed.

  Lemma optimize_csubst {a k b} n :
    wf_glob Σ ->
    wellformed Σ (k + n) b ->
    optimize (ECSubst.csubst a k b) = ECSubst.csubst (optimize a) k (optimize b).
  Proof using Type wfm wca.
    intros wfΣ.
    induction b in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros wft; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold wf_fix, test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - destruct (k ?= n0)%nat; auto.
    - f_equal. rtoProp. rewrite wca in H0. now destruct args; inv H0.
    - move/andP: wft => [] hasc /andP[] /andP[] hi hb hl. rewrite IHb. f_equal. unfold on_snd; solve_all.
      repeat toAll. f_equal. solve_all.
      rewrite -!reorder_branches_map map_map_compose. cbn. f_equal.
      unfold on_snd; cbn.
      solve_all. f_equal. unfold optimize in *.
      rewrite a0 //. red; rewrite -b0. lia_f_equal.
    - move/andP: wft => [] /andP[] hasf hp /andP[] hb hwfm.
      f_equal. solve_all.
      rewrite /map_def; destruct x => //=. f_equal.
      apply a0; cbn in *. red; rewrite -b0. lia_f_equal.
    - move/andP: wft => [] hasco /andP[] hp hb.
      f_equal. solve_all.
      rewrite /map_def; destruct x => //=. f_equal.
      apply a0; cbn in *. red; rewrite -b. lia_f_equal.
  Qed.

  Lemma optimize_substl s t :
    wf_glob Σ ->
    forallb (wellformed Σ 0) s ->
    wellformed Σ #|s| t ->
    optimize (substl s t) = substl (map optimize s) (optimize t).
  Proof using Type wfm wca.
    intros wfΣ. induction s in t |- *; simpl; auto.
    move/andP => [] cla cls wft.
    rewrite IHs //. eapply wellformed_csubst => //.
    f_equal. rewrite (optimize_csubst (S #|s|)) //.
  Qed.

  Lemma optimize_iota_red pars args br :
    wf_glob Σ ->
    forallb (wellformed Σ 0) args ->
    wellformed Σ #|skipn pars args| br.2 ->
    optimize (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map optimize args) (on_snd optimize br).
  Proof using Type wfm wca.
    intros wfΣ wfa wfbr.
    unfold EGlobalEnv.iota_red.
    rewrite optimize_substl //.
    rewrite forallb_rev forallb_skipn //.
    now rewrite List.length_rev.
    now rewrite map_rev map_skipn.
  Qed.

  Lemma optimize_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def optimize) mfix) = map optimize (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def optimize) mfix) = map optimize (EGlobalEnv.cofix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.cofix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cunfold_fix mfix idx n f :
    wf_glob Σ ->
    wellformed Σ 0 (tFix mfix idx) ->
    cunfold_fix mfix idx = Some (n, f) ->
    cunfold_fix (map (map_def optimize) mfix) idx = Some (n, optimize f).
  Proof using Type wfm wca.
    intros wfΣ hfix.
    unfold cunfold_fix.
    rewrite nth_error_map.
    cbn in hfix. move/andP: hfix => [] /andP[] hasfix hlam /andP[] hidx hfix.
    destruct nth_error eqn:hnth => //.
    intros [= <- <-] => /=. f_equal.
    rewrite optimize_substl //. eapply wellformed_fix_subst => //.
    rewrite fix_subst_length.
    eapply nth_error_forallb in hfix; tea. now rewrite Nat.add_0_r in hfix.
    now rewrite optimize_fix_subst.
  Qed.

  Lemma optimize_cunfold_cofix mfix idx n f :
    wf_glob Σ ->
    wellformed Σ 0 (tCoFix mfix idx) ->
    cunfold_cofix mfix idx = Some (n, f) ->
    cunfold_cofix (map (map_def optimize) mfix) idx = Some (n, optimize f).
  Proof using Type wfm wca.
    intros wfΣ hfix.
    unfold cunfold_cofix.
    rewrite nth_error_map.
    cbn in hfix. move/andP: hfix => [] hasfix /andP[] hidx hfix.
    destruct nth_error eqn:hnth => //.
    intros [= <- <-] => /=. f_equal.
    rewrite optimize_substl //. eapply wellformed_cofix_subst => //.
    rewrite cofix_subst_length.
    eapply nth_error_forallb in hfix; tea. now rewrite Nat.add_0_r in hfix.
    now rewrite optimize_cofix_subst.
  Qed.

End reorder_proofs.

Import EGlobalEnv EExtends.

Lemma extends_lookup_projection {efl : EEnvFlags} {Σ Σ' p} : extends Σ Σ' -> wf_glob Σ' ->
  isSome (lookup_projection Σ p) ->
  lookup_projection Σ p = lookup_projection Σ' p.
Proof.
  intros ext wf.
  unfold lookup_projection.
  destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
  simpl.
  rewrite (extends_lookup_constructor wf ext _ _ _ hl) //.
Qed.

(*
Lemma wellformed_optimize_extends {wfl: EEnvFlags} {Σ} t :
  forall n, EWellformed.wellformed Σ n t ->
  forall {Σ'}, extends Σ Σ' -> wf_glob Σ' ->
  optimize Σ t = optimize Σ' t.
Proof.
  induction t using EInduction.term_forall_list_ind; cbn -[lookup_constant lookup_inductive
    GlobalContextMap.lookup_projection]; intros => //.
  all:unfold wf_fix_gen in *; rtoProp; intuition auto.
  5:{ destruct cstr_as_blocks; rtoProp. f_equal; eauto; solve_all. destruct args; cbn in *; eauto. }
  all:f_equal; eauto; solve_all.
  - rewrite !GlobalContextMap.lookup_projection_spec.
    rewrite -(extends_lookup_projection H0 H1 H3).
    destruct lookup_projection as [[[[]]]|]. f_equal; eauto.
    now cbn in H3.
Qed.

Lemma wellformed_reorder_decl_extends {wfl: EEnvFlags} {Σ} t :
  wf_global_decl Σ t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  reorder_decl Σ t = reorder_decl Σ' t.
Proof.
  destruct t => /= //.
  intros wf Σ' ext wf'. f_equal. unfold optimize_constant_decl. f_equal.
  destruct (cst_body c) => /= //. f_equal.
  now eapply wellformed_optimize_extends.
Qed.

Lemma lookup_env_reorder_env_Some {efl : EEnvFlags} {Σ} kn d :
  wf_glob Σ ->
  GlobalContextMap.lookup_env Σ kn = Some d ->
  ∑ Σ' : GlobalContextMap.t,
    [× extends_prefix Σ' Σ, wf_global_decl Σ' d &
      lookup_env (reorder_env Σ) kn = Some (reorder_decl Σ' d)].
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  induction Σ in map, repr, wf |- *; simpl; auto => //.
  intros wfg.
  case: eqb_specT => //.
  - intros ->. cbn. intros [= <-].
    exists (GlobalContextMap.make Σ (fresh_globals_cons_inv wf)). split.
    now eexists [_].
    cbn. now depelim wfg.
    f_equal. symmetry. eapply wellformed_reorder_decl_extends. cbn. now depelim wfg.
    eapply extends_prefix_extends.
    cbn. now exists [a]. now cbn. now cbn.
  - intros _.
    set (Σ' := GlobalContextMap.make Σ (fresh_globals_cons_inv wf)).
    specialize (IHΣ (GlobalContextMap.map Σ') (GlobalContextMap.repr Σ') (GlobalContextMap.wf Σ')).
    cbn in IHΣ. forward IHΣ. now depelim wfg.
    intros hl. specialize (IHΣ hl) as [Σ'' [ext wfgd hl']].
    exists Σ''. split => //.
    * destruct ext as [? ->].
      now exists (a :: x).
    * rewrite -hl'. f_equal.
      clear -wfg.
      eapply map_ext_in => kn hin. unfold on_snd. f_equal.
      symmetry. eapply wellformed_reorder_decl_extends => //. cbn.
      eapply lookup_env_In in hin. 2:now depelim wfg.
      depelim wfg. eapply lookup_env_wellformed; tea.
      eapply extends_prefix_extends.
      cbn. now exists [a]. now cbn.
Qed.

Lemma lookup_env_map_snd Σ f kn : lookup_env (List.map (on_snd f) Σ) kn = option_map f (lookup_env Σ kn).
Proof.
  induction Σ; cbn; auto.
  case: eqb_spec => //.
Qed.

Lemma lookup_env_reorder_env_None {efl : EEnvFlags} {Σ} kn :
  GlobalContextMap.lookup_env Σ kn = None ->
  lookup_env (reorder_env Σ) kn = None.
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  cbn. intros hl. rewrite lookup_env_map_snd hl //.
Qed.
*)

Section reorder_mapping.
  Context {efl : EEnvFlags}.
  Context {wca : cstr_as_blocks = false}.

  Context (mapping : inductives_mapping).
  Context (Σ : global_context).
  Context (wfm : wf_inductives_mapping Σ mapping).
  Notation reorder := (reorder mapping).
  Notation reorder_decl := (reorder_decl mapping).
  Notation reorder_env := (reorder_env mapping).

Lemma is_propositional_optimize ind :
  wf_glob Σ ->
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars (reorder_env Σ) ind.
Proof.
  rewrite /inductive_isprop_and_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite lookup_env_reorder.
  destruct lookup_env as [[decl|]|] => //=.
  rewrite nth_error_mapi. destruct nth_error => //=.
  destruct o => //=. rewrite /reorder_one_ind /=.
  destruct lookup_inductive_assoc as [[na tags]|]=> //=.
Qed.

Lemma lookup_inductive_pars_optimize ind :
  wf_glob Σ ->
  EGlobalEnv.lookup_inductive_pars Σ ind = EGlobalEnv.lookup_inductive_pars (reorder_env Σ) ind.
Proof.
  rewrite /lookup_inductive_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite lookup_env_reorder.
  destruct lookup_env as [[decl|]|] => //.
Qed.

Lemma is_propositional_cstr_optimize ind c :
  wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = constructor_isprop_pars_decl (reorder_env Σ) ind (lookup_constructor_ordinal mapping ind c).
Proof.
  rewrite /constructor_isprop_pars_decl => wf.
  rewrite -lookup_constructor_reorder //.
  destruct lookup_constructor as [[[mib oib] cb]|] => //=.
  rewrite /reorder_one_ind.
  destruct lookup_inductive_assoc as [[na tags]|]=> //.
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
  now rewrite List.length_rev hskip Nat.add_0_r.
Qed.

Lemma isFix_mkApps t l : isFix (mkApps t l) = isFix t && match l with [] => true | _ => false end.
Proof.
  induction l using rev_ind; cbn.
  - now rewrite andb_true_r.
  - rewrite mkApps_app /=. now destruct l => /= //; rewrite andb_false_r.
Qed.

Lemma constructor_isprop_pars_decl_inductive {ind c} {prop pars cdecl} :
  constructor_isprop_pars_decl Σ ind c = Some (prop, pars, cdecl)  ->
  inductive_isprop_and_pars Σ ind = Some (prop, pars).
Proof.
  rewrite /constructor_isprop_pars_decl /inductive_isprop_and_pars /lookup_constructor.
  destruct lookup_inductive as [[mdecl idecl]|]=> /= //.
  destruct nth_error => //. congruence.
Qed.

Lemma constructor_isprop_pars_decl_constructor {ind c} {mdecl idecl cdecl} :
  lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
  constructor_isprop_pars_decl Σ ind c = Some (ind_propositional idecl, ind_npars mdecl, cdecl).
Proof.
  rewrite /constructor_isprop_pars_decl. intros -> => /= //.
Qed.

Lemma wf_mkApps {hasapp : has_tApp} k f args :
  reflect (wellformed Σ k f /\ forallb (wellformed Σ k) args) (wellformed Σ k (mkApps f args)).
Proof.
  rewrite wellformed_mkApps //. eapply andP.
Qed.

Lemma substl_closed s t : closed t -> substl s t = t.
Proof.
  induction s in t |- *; cbn => //.
  intros clt. rewrite csubst_closed //. now apply IHs.
Qed.

Lemma substl_rel s k a :
  closed a ->
  nth_error s k = Some a ->
  substl s (tRel k) = a.
Proof.
  intros cla.
  induction s in k |- *.
  - rewrite nth_error_nil //.
  - destruct k => //=.
    * intros [= ->]. rewrite substl_closed //.
    * intros hnth. now apply IHs.
Qed.

(* EEnvFlags is reorder_env_flags *)
Lemma optimize_correct {fl} t v {withc : with_constructor_as_block = false} :
  has_tApp ->
  wf_glob Σ ->
  @eval fl Σ t v ->
  wellformed Σ 0 t ->
  @eval fl (reorder_env Σ) (reorder t) (reorder v).
Proof.
  intros hastapp wfΣ ev.
  induction ev; simpl in *.

  - move/andP => [] /andP[] hasapp cla clt. econstructor; eauto.
  - move/andP => [] /andP[] hasapp clf cla.
    eapply eval_wellformed in ev2; tea => //.
    eapply eval_wellformed in ev1; tea => //.
    econstructor; eauto.
    move: ev1 => /= /andP[] hasl ev1.
    rewrite -(optimize_csubst _ _ wfm 1) //.
    apply IHev3. eapply wellformed_csubst => //.

  - move/andP => [] /andP[] haslet clb0 clb1.
    intuition auto.
    eapply eval_wellformed in ev1; tea => //.
    forward IHev2 by eapply wellformed_csubst => //.
    econstructor; eauto. rewrite -(optimize_csubst _ _ wfm 1) //.

  - move/andP => [] hascase /andP[] /andP[] hl wfd wfbrs.
    rewrite optimize_mkApps in IHev1.
    eapply eval_wellformed in ev1 => //.
    move/(@wf_mkApps hastapp): ev1 => [] wfc' wfargs.
    eapply nth_error_forallb in wfbrs; tea.
    rewrite Nat.add_0_r in wfbrs.
    forward IHev2. eapply wellformed_iota_red; tea => //.
    rewrite (optimize_iota_red _ _ wfm) in IHev2 => //. now rewrite e4.
    econstructor; eauto.
    rewrite -is_propositional_cstr_optimize //. tea.
    rewrite reorder_branches_map nth_error_map.
    rewrite /reorder_branches.
    rewrite /lookup_constructor_ordinal /lookup_constructor_mapping.
    destruct lookup_inductive_assoc as [[na tags]|] eqn:hla => //=.
    rewrite /wf_brs in hl.
    destruct lookup_inductive as [[mib oib]|] eqn:li => //. apply Nat.eqb_eq in hl.
    have wftags := lookup_inductive_assoc_wf_tags _ _ wfm li hla.
    have wfmap := lookup_inductive_assoc_spec _ _ wfm hla.
    have wfbrl : #|brs| = #|ind_ctors oib|. lia.
    have wftbrs : wf_tags_list tags #|brs|.
    { now move: wftags; rewrite /wf_tags_list -wfbrl. }
    destruct new_tag eqn:hnewt => //=.
    * eapply new_tag_spec in hnewt.
      rewrite (nth_error_reorder wftbrs hnewt) e2 //.
    * move: wftbrs => /andP[] htbrs wftag.
      eapply find_tag_wf in wftag; tea. apply nth_error_Some_length in e2.
      apply eqb_eq in htbrs. lia.
    * rewrite e2 //.
    * len.
    * len.

  - congruence.

  - move/andP => [] hascase /andP[] /andP[] hl wfd wfbrs.
    eapply eval_wellformed in ev1 => //.
    move: hl; rewrite /wf_brs.
    destruct lookup_inductive as [[mib oib]|] eqn:li => //. move/Nat.eqb_eq.
    len. cbn in wfbrs. subst brs. cbn in wfbrs. rewrite Nat.add_0_r in wfbrs.
    move/andP: wfbrs => [] wfbrs _. cbn; intros hlen.
    forward IHev2. eapply wellformed_substl; tea => //.
    rewrite forallb_repeat //. len.
    eapply eval_iota_sing; eauto.
    rewrite -is_propositional_optimize //.
    rewrite /reorder_branches.
    destruct lookup_inductive_assoc as [[na tags]|] eqn:hla => //=.
    have wftags := lookup_inductive_assoc_wf_tags _ _ wfm li hla.
    have wfmap := lookup_inductive_assoc_spec _ _ wfm hla.
    have wftbrs : wf_tags_list tags #|[(n, f4)]|.
    { move: wftags; rewrite /wf_tags_list //=. now rewrite hlen. }
    rewrite //=.
    move: wftbrs => /andP[] /Nat.eqb_eq //=.
    destruct tags => //=. destruct tags => //= _.
    rewrite /wf_tags => /andP[] ht _. move: ht => //= /andP[] /Nat.ltb_lt.
    destruct n0 => //. destruct n0 => //. cbn -[substl].
    rewrite (optimize_substl Σ) in IHev2 => //.
    * now rewrite forallb_repeat.
    * now len.
    * now rewrite map_repeat in IHev2.

  - move/andP => [] /andP[] hasapp clf cla. rewrite optimize_mkApps in IHev1.
    simpl in *.
    eapply eval_wellformed in ev1 => //.
    move/(@wf_mkApps hastapp): ev1 => [] wff wfargs.
    eapply eval_fix; eauto.
    rewrite length_map.
    unshelve (eapply optimize_cunfold_fix; tea); tea.
    rewrite optimize_mkApps in IHev3. apply IHev3.
    rewrite wellformed_mkApps // wfargs.
    eapply eval_wellformed in ev2; tas => //. rewrite ev2 /= !andb_true_r.
    rewrite hastapp.
    eapply wellformed_cunfold_fix; tea.

  - move/andP => [] /andP[] hasapp clf cla.
    eapply eval_wellformed in ev1 => //.
    move/(@wf_mkApps hastapp): ev1 => [] clfix clargs.
    eapply eval_wellformed in ev2; tas => //.
    rewrite optimize_mkApps in IHev1 |- *.
    simpl in *. eapply eval_fix_value. auto. auto. auto.
    unshelve (eapply optimize_cunfold_fix; eauto); tea.
    now rewrite length_map.

  - move/andP => [] /andP[] hasapp clf cla.
    eapply eval_wellformed in ev1 => //.
    eapply eval_wellformed in ev2; tas => //.
    simpl in *. eapply eval_fix'. auto. auto.
    unshelve (eapply optimize_cunfold_fix; eauto); tea.
    eapply IHev2; tea. eapply IHev3.
    apply/andP; split => //.
    rewrite hastapp.
    eapply wellformed_cunfold_fix; tea.

  - move/andP => [] hascase /andP[] /andP[] hl cd clbrs. specialize (IHev1 cd).
    eapply eval_wellformed in ev1; tea => //.
    move/(@wf_mkApps hastapp): ev1 => [] wfcof wfargs.
    forward IHev2.
    rewrite hl wellformed_mkApps // /= wfargs clbrs !andb_true_r.
    rewrite hascase.
    eapply wellformed_cunfold_cofix; tea => //.
    rewrite !optimize_mkApps /= in IHev1, IHev2.
    eapply eval_cofix_case. tea.
    unshelve (eapply optimize_cunfold_cofix; tea); tea.
    exact IHev2.

  - move/andP => [] /andP[] hasproj hl hd.
    destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl' => //.
    eapply eval_wellformed in ev1 => //.
    move/(@wf_mkApps hastapp): ev1 => [] wfcof wfargs.
    forward IHev2.
    { rewrite /= wellformed_mkApps // wfargs andb_true_r hasproj andb_true_r.
      eapply wellformed_cunfold_cofix; tea. }
    rewrite optimize_mkApps /= in IHev1.
    eapply eval_cofix_proj. eauto.
    unshelve (eapply optimize_cunfold_cofix; tea); tea.
    rewrite optimize_mkApps in IHev2 => //.

  - rewrite /declared_constant in isdecl.
    rewrite /lookup_constant. rewrite isdecl /= => _.
    destruct decl; cbn in e; subst cst_body.
    econstructor.
    rewrite /declared_constant.
    rewrite lookup_env_reorder isdecl //=. cbn. reflexivity.
    eapply IHev.
    eapply lookup_env_wellformed in wfΣ; tea.
    move: wfΣ. now rewrite /wf_global_decl /=.

  - move=> /andP[] /andP[] hasproj iss cld.
    eapply eval_wellformed in ev1; tea => //.
    move/(@wf_mkApps hastapp): ev1 => [] wfc wfargs.
    destruct lookup_projection as [[[[mdecl idecl] cdecl'] pdecl]|] eqn:hl' => //.
    pose proof (lookup_projection_lookup_constructor hl').
    rewrite (constructor_isprop_pars_decl_constructor H) in e1. noconf e1.
    forward IHev1 by auto.
    forward IHev2. eapply nth_error_forallb in wfargs; tea.
    rewrite optimize_mkApps /= in IHev1.
    have lp := lookup_projection_reorder _ _ wfm p wfΣ.
    forward lp. now rewrite hl'.
    rewrite hl' /= in lp.
    have lpo := (lookup_projection_ordinal _ _ wfm p wfΣ).
    forward lpo by now rewrite hl'.
    rewrite lpo in IHev1.
    eapply eval_proj; tea.
    rewrite -lpo -is_propositional_cstr_optimize //.
    rewrite /constructor_isprop_pars_decl // H //= // H0 H1 //.
    len. rewrite nth_error_map e3 //.

  - congruence.

  - move/andP => [] /andP[] hasproj hl hd.
    eapply eval_proj_prop; eauto.
    rewrite -is_propositional_optimize //.

  - move/andP=> [] /andP[] hasapp clf cla.
    rewrite optimize_mkApps.
    eapply eval_construct; tea.
    rewrite -lookup_constructor_reorder //. now rewrite e0 //=.
    rewrite optimize_mkApps in IHev1. now eapply IHev1.
    now len.
    now eapply IHev2.

  - congruence.

  - move/andP => [] /andP[] hasapp clf cla.
    specialize (IHev1 clf). specialize (IHev2 cla).
    eapply eval_app_cong; eauto.
    eapply eval_to_value in ev1.
    destruct ev1; simpl in *; eauto.
    * depelim a0.
      + destruct t => //; rewrite optimize_mkApps /=.
      + now rewrite /= !orb_false_r orb_true_r in i.
    * destruct with_guarded_fix.
      + move: i.
        rewrite !negb_or.
        rewrite optimize_mkApps !isFixApp_mkApps !isConstructApp_mkApps !isPrimApp_mkApps
          !isLazyApp_mkApps.
        destruct args using rev_case => // /=. rewrite map_app !mkApps_app /= //.
        rewrite !andb_true_r.
        rtoProp; intuition auto;  destruct v => /= //.
      + move: i.
        rewrite !negb_or.
        rewrite optimize_mkApps !isConstructApp_mkApps !isPrimApp_mkApps !isLazyApp_mkApps.
        destruct args using rev_case => // /=. rewrite map_app !mkApps_app /= //.
        destruct v => /= //.
  - intros; rtoProp; intuition eauto.
    depelim X; repeat constructor.
    eapply All2_over_undep in a.
    eapply All2_Set_All2 in ev. eapply All2_All2_Set. primProp.
    subst a0 a'; cbn in *. depelim H0; cbn in *. intuition auto; solve_all.
    primProp; depelim H0; intuition eauto.
  - move=> /andP[] haslazy wf. econstructor; eauto. eapply IHev2.
    eapply eval_wellformed in ev1; tea. move/andP: ev1 => []; tea => //.
  - destruct t => //.
    all:constructor; eauto.
    cbn [atom reorder] in i |- *.
    rewrite -lookup_constructor_reorder //.
    destruct args. 2:cbn in *; eauto.
    cbn -[lookup_constructor]. rtoProp; intuition auto.
    destruct lookup_constructor => //.
Qed.
End reorder_mapping.

Lemma wf_inductive_mapping_inv {efl : EEnvFlags} d Σ m :
  wf_glob (d :: Σ) ->
  wf_inductives_mapping (d :: Σ) m ->
  (match d.2 with
  | InductiveDecl mib =>
    (forall i oib, nth_error mib.(ind_bodies) i = Some oib ->
     match lookup_inductive_assoc m {| inductive_mind := d.1; inductive_ind := i |} with
    | Some (na, tags) => wf_tags_list tags #|oib.(ind_ctors)|
    | None => true
    end)
  | ConstantDecl _ => True
  end) /\ wf_inductives_mapping Σ m.
Proof.
  rewrite /wf_inductives_mapping.
  intros wfΣ wfm. split; revgoals. solve_all.
  move: H; rewrite /wf_inductive_mapping.
  destruct x as [ind [na tags]].
  destruct lookup_inductive as [[mib oib]|] eqn:li => //=.
  depelim wfΣ; cbn.
  move: li. cbn. case: eqb_spec.
  * intros <-.
    destruct d0 => //. destruct nth_error eqn:hnth => //.
    intros [= -> ->].
    destruct lookup_env eqn:hle.
    have:= lookup_env_Some_fresh hle. contradiction.
    auto.
  * intros neq. destruct lookup_env => //=. destruct g => //.
    destruct nth_error => //. now intros [= -> ->].
  * depelim wfΣ. move: li. cbn; case: eqb_spec.
    + intros <-. destruct d0 => //.
      destruct lookup_env eqn:hle => //.
      have:= lookup_env_Some_fresh hle. contradiction.
      destruct lookup_env eqn:hle => //.
      have:= lookup_env_Some_fresh hle. contradiction.
    + intros neq. destruct lookup_env => //=. destruct g => //.
      destruct nth_error => //.
  * depelim wfΣ; cbn.
    destruct d0 => //.
    intros i oib hnth.
    destruct lookup_inductive_assoc as [[na tags]|] eqn:hla => //.
    have hla' := lookup_inductive_assoc_wf_tags _ _ wfm _ hla.
    eapply hla'.
    rewrite /lookup_inductive /lookup_minductive /=.
    rewrite eqb_refl. rewrite hnth. reflexivity.
Qed.

From MetaRocq.Erasure Require Import EEtaExpanded.

Lemma optimize_expanded {Σ m} t :
  wf_inductives_mapping Σ m -> expanded Σ t -> expanded (reorder_env m Σ) (reorder m t).
Proof.
  intros wfm.
  induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  all:rewrite ?optimize_mkApps.
  - eapply expanded_mkApps_expanded => //. solve_all.
  - cbn. econstructor; eauto.
    rewrite /reorder_branches.
    destruct lookup_inductive_assoc => //; solve_all.
    eapply All_reorder_list. solve_all.
  - cbn. eapply expanded_tFix. solve_all.
    rewrite isLambda_optimize //.
  - cbn.
    eapply declared_constructor_lookup in H.
    have hl := lookup_constructor_reorder _ _ wfm ind idx. rewrite H /= in hl.
    eapply expanded_tConstruct_app; tea.
    eapply lookup_declared_constructor. now symmetry.
    now len. now solve_all.
Qed.

Lemma optimize_expanded_decl {Σ m kn t} :
  wf_inductives_mapping Σ m ->
  expanded_decl Σ t -> expanded_decl (reorder_env m Σ) (reorder_decl m (kn, t)).2.
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  intros. now apply optimize_expanded.
Qed.

Lemma reorder_env_expanded {efl : EEnvFlags} {Σ m} :
  wf_inductives_mapping Σ m ->
  wf_glob Σ -> expanded_global_env Σ -> expanded_global_env (reorder_env m Σ).
Proof.
  intros wfm.
  unfold expanded_global_env; move=> wfg exp.
  induction exp; cbn; constructor; auto.
  cbn in IHexp.
  unshelve eapply IHexp; tea. eapply wf_inductive_mapping_inv; tea. now depelim wfg. cbn.
  unshelve eapply (optimize_expanded_decl). now eapply wf_inductive_mapping_inv.
  now destruct decl.
Qed.

From MetaRocq.Erasure Require Import EEtaExpandedFix.

Lemma optimize_expanded_fix {Σ Γ m} t :
  wf_inductives_mapping Σ m -> expanded Σ Γ t -> expanded (reorder_env m Σ) Γ (reorder m t).
Proof.
  intros wfm.
  induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  all:rewrite ?optimize_mkApps.
  - cbn. eapply expanded_tRel_app; tea. len. solve_all.
  - cbn. econstructor; eauto.
    2:solve_all.
    destruct f3 => //.
  - cbn. econstructor; eauto.
    rewrite /reorder_branches.
    destruct lookup_inductive_assoc => //; solve_all.
    eapply All_reorder_list. solve_all.
  - cbn. eapply expanded_tFix. solve_all.
    rewrite isLambda_optimize //.
    now rewrite rev_map_spec map_map_compose /= -rev_map_spec.
    solve_all. destruct args => //. rewrite nth_error_map /= H4 //.
    len.
  - cbn.
    eapply declared_constructor_lookup in H.
    have hl := lookup_constructor_reorder _ _ wfm ind idx. rewrite H /= in hl.
    eapply expanded_tConstruct_app; tea.
    eapply lookup_declared_constructor. now symmetry.
    now len. now solve_all.
Qed.

Lemma optimize_expanded_decl_fix {Σ m kn t} :
  wf_inductives_mapping Σ m ->
  expanded_decl Σ t -> expanded_decl (reorder_env m Σ) (reorder_decl m (kn, t)).2.
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  intros. now apply optimize_expanded_fix.
Qed.

Lemma reorder_env_expanded_fix {efl : EEnvFlags} {Σ m} :
  wf_inductives_mapping Σ m ->
  wf_glob Σ -> expanded_global_env Σ -> expanded_global_env (reorder_env m Σ).
Proof.
  intros wfm.
  unfold expanded_global_env; move=> wfg exp.
  induction exp; cbn; constructor; auto.
  cbn in IHexp.
  unshelve eapply IHexp; tea. eapply wf_inductive_mapping_inv; tea. now depelim wfg. cbn.
  unshelve eapply (optimize_expanded_decl_fix). now eapply wf_inductive_mapping_inv.
  now destruct decl.
Qed.

Lemma optimize_extends_env {efl : EEnvFlags} {Σ Σ'} m :
  wf_inductives_mapping Σ' m ->
  extends Σ Σ' ->
  wf_glob Σ ->
  wf_glob Σ' ->
  extends (reorder_env m Σ) (reorder_env m Σ').
Proof.
  intros hast ext wf wf'.
  rewrite /extends => kn decl.
  rewrite !lookup_env_reorder.
  specialize (ext kn).
  destruct lookup_env eqn:hle => //. specialize (ext _ eq_refl).
  rewrite ext. auto.
Qed.

Lemma reorder_env_wf {efl : EEnvFlags} {Σ m}
  {wcb : cstr_as_blocks = false} :
  wf_inductives_mapping Σ m ->
  wf_glob Σ -> wf_glob (reorder_env m Σ).
Proof.
  intros wfg wfΣ.
  induction wfΣ; cbn. constructor; eauto.
  have wfdΣ : (wf_glob ((kn, d) :: Σ)) by constructor; auto.
  have [wfd wfinv] := (wf_inductive_mapping_inv _ _ _ wfdΣ wfg). cbn in wfd.
  constructor; eauto. destruct d; cbn.
  - unfold wf_global_decl in H. cbn in H.
    destruct (cst_body c) => //=. cbn in H.
    unshelve (eapply wf_optimize); eauto.
  - cbn in H. rewrite /wf_minductive in H. cbn in H.
    rewrite /wf_minductive /=.
    move/andP: H => [] -> H /=. solve_all.
    have hfa := (forall_nth_error_Alli (fun i oib =>
    is_true (match lookup_inductive_assoc m {| inductive_mind := kn; inductive_ind := i |} with
    | Some p => let (_, tags) := p in wf_tags_list tags #|ind_ctors oib|
    | None => true
    end)) 0 (ind_bodies m0) wfd). clear wfd.
    eapply Alli_All_mix in hfa; tea. clear H.
    eapply (Alli_All (P:=fun _ x => wf_inductive x) (n:=0)); eauto.
    eapply (fst (Alli_mapi _ _ _)).
    eapply Alli_impl; tea. cbn.
    intros n x [hla wf].
    rewrite /reorder_one_ind.
    destruct lookup_inductive_assoc as [[na tags]|] eqn:hla' => //.
    move: wf. rewrite /wf_inductive /wf_projections /=.
    destruct ind_projs => //. destruct ind_ctors => //. destruct l0 => //=.
    move: hla; rewrite /wf_tags_list. destruct tags => //=.
    destruct tags => //=. rewrite /wf_tags. move/andP=> [] hf _.
    cbn in hf. rewrite andb_true_r in hf. apply Nat.leb_le in hf.
    have -> : n0 = 0 by lia. now cbn.
  - cbn. apply ErasureFunction.fresh_global_In.
    rewrite map_map_compose /=. intros hin'. apply ErasureFunction.fresh_global_In in H0.
    now apply H0.
Qed.

From MetaRocq.Erasure Require Import EProgram.

Definition reorder_program_wf {efl : EEnvFlags} {wca : cstr_as_blocks = false} (p : eprogram) m (wfm : wf_inductives_mapping p.1 m) :
  wf_eprogram efl p -> wf_eprogram efl (reorder_program m p).
Proof.
  intros []; split.
  now unshelve eapply reorder_env_wf.
  cbn. now eapply (@wf_optimize _ _ wfm efl wca).
Qed.

Definition reorder_program_expanded {efl : EEnvFlags} (p : eprogram) m (wfm : wf_inductives_mapping p.1 m) :
  wf_eprogram efl p ->
  expanded_eprogram_cstrs p -> expanded_eprogram_cstrs (reorder_program m p).
Proof.
  unfold expanded_eprogram_env_cstrs.
  move=> [wfe wft] /andP[] etae etat.
  apply/andP; split.
  cbn. eapply EEtaExpanded.expanded_global_env_isEtaExp_env, reorder_env_expanded => //.
  now eapply isEtaExp_env_expanded_global_env.
  eapply EEtaExpanded.expanded_isEtaExp.
  now apply optimize_expanded, EEtaExpanded.isEtaExp_expanded.
Qed.

Definition reorder_program_expanded_fix {efl : EEnvFlags} (p : eprogram) m (wfm : wf_inductives_mapping p.1 m) :
  wf_eprogram efl p ->
  expanded_eprogram p -> expanded_eprogram (reorder_program m p).
Proof.
  unfold expanded_eprogram.
  move=> [wfe wft] [] etae etat.
  split. now eapply reorder_env_expanded_fix.
  now eapply optimize_expanded_fix.
Qed.
