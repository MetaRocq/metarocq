(* Distributed under the terms of the MIT license. *)
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst.
From Stdlib Require Import ssreflect ssrbool.

Global Hint Resolve app_tip_nil : core.

Fixpoint decompose_app_rec t l :=
  match t with
  | tApp f a => decompose_app_rec f (a :: l)
  | f => (f, l)
  end.

Definition decompose_app f := decompose_app_rec f [].

Definition head t := fst (decompose_app t).
Definition spine t := snd (decompose_app t).

Lemma decompose_app_head_spine t : decompose_app t = (head t, spine t).
Proof.
  unfold head, spine.
  destruct decompose_app => //.
Qed.

Lemma decompose_app_rec_mkApps f l l' :
  decompose_app_rec (mkApps f l) l' = decompose_app_rec f (l ++ l').
Proof.
  induction l in f, l' |- *; simpl; auto; rewrite IHl ?app_nil_r; auto.
Qed.

Lemma decompose_app_mkApps f l :
  ~~ isApp f -> decompose_app (mkApps f l) = (f, l).
Proof.
  intros Hf. unfold decompose_app. rewrite decompose_app_rec_mkApps. rewrite app_nil_r.
  destruct f; simpl in *; (discriminate || reflexivity).
Qed.

Lemma mkApps_app t l l' : mkApps t (l ++ l') = mkApps (mkApps t l) l'.
Proof.
  induction l in t, l' |- *; simpl; auto.
Qed.

Lemma decompose_app_rec_inv {t l' f l} :
  decompose_app_rec t l' = (f, l) ->
  mkApps t l' = mkApps f l.
Proof.
  induction t in f, l', l |- *; try intros [= <- <-]; try reflexivity.
  simpl. apply/IHt1.
Qed.

Lemma decompose_app_inv {t f l} :
  decompose_app t = (f, l) -> t = mkApps f l.
Proof. by apply/decompose_app_rec_inv. Qed.

Lemma head_mkApps f a : head (mkApps f a) = head f.
Proof.
  rewrite /head /decompose_app /=.
  rewrite decompose_app_rec_mkApps /= app_nil_r.
  induction f in a |- *; simpl; auto.
  now rewrite !IHf1.
Qed.

Lemma head_tApp f a : head (tApp f a) = head f.
Proof.
  eapply (head_mkApps f [a]).
Qed.

Lemma nApp_decompose_app t l : ~~ isApp t -> decompose_app_rec t l = pair t l.
Proof. destruct t; simpl; congruence. Qed.

Lemma decompose_app_rec_notApp :
  forall t l u l',
    decompose_app_rec t l = (u, l') ->
    ~~ isApp u.
Proof.
  intros t l u l' e.
  induction t in l, u, l', e |- *.
  all: try (cbn in e ; inversion e ; reflexivity).
  cbn in e. eapply IHt1. eassumption.
Qed.

Lemma decompose_app_notApp :
  forall t u l,
    decompose_app t = (u, l) ->
    ~~ isApp u.
Proof.
  intros t u l e.
  eapply decompose_app_rec_notApp. eassumption.
Qed.

Lemma head_nApp t : ~~ isApp (head t).
Proof.
  rewrite /head. destruct decompose_app eqn:da => //=.
  now eapply decompose_app_notApp.
Qed.

Global Hint Resolve head_nApp : core.

Lemma spine_mkApps f a : spine (mkApps f a) = spine f ++ a.
Proof.
  rewrite /spine /decompose_app /=.
  rewrite decompose_app_rec_mkApps /= app_nil_r.
  destruct (decompose_app_rec f []) eqn:da. cbn.
  rewrite (decompose_app_inv da).
  rewrite decompose_app_rec_mkApps.
  rewrite nApp_decompose_app.
  eapply decompose_app_rec_notApp; tea. now cbn.
Qed.

Lemma spine_tApp f a : spine (tApp f a) = spine f ++ [a].
Proof.
  eapply (spine_mkApps f [a]).
Qed.

Lemma spine_nApp f : ~~ isApp f -> spine f = [].
Proof.
  destruct f => //.
Qed.

Lemma mkApps_head_spine t : mkApps (head t) (spine t) = t.
Proof. induction t => //. rewrite head_tApp /=.
  rewrite spine_tApp mkApps_app /=. f_equal. auto.
Qed.

Lemma mkApps_head_spine_decompose f l : mkApps f l = mkApps (head f) (spine f ++ l).
Proof.
  now rewrite mkApps_app mkApps_head_spine.
Qed.

Lemma mkApps_eq_decompose_app_rec {f args t l} :
  mkApps f args = t ->
  ~~ isApp f ->
  match decompose_app_rec t l with
  | (f', args') => f' = f /\ mkApps t l = mkApps f' args'
  end.
Proof.
  revert f t l.
  induction args using rev_ind; simpl.
  - intros * -> **. rewrite nApp_decompose_app; auto.
  - intros. rewrite mkApps_app in H.
    specialize (IHargs f).
    destruct (isApp t) eqn:Heq.
    destruct t; try discriminate.
    simpl in Heq. inv H. simpl.
    specialize (IHargs (mkApps f args) (t2 :: l) eq_refl H0).
    destruct decompose_app_rec. intuition.
    subst t.
    simpl in Heq. discriminate.
Qed.

Lemma decompose_app_eq_right t l l' : decompose_app_rec t l = decompose_app_rec t l' -> l = l'.
Proof.
  induction t in l, l' |- *; simpl; intros [=]; auto.
  specialize (IHt1 _ _ H0). now inv IHt1.
Qed.

Lemma head_nApp_eq {t} : ~~ isApp t -> head t = t.
Proof.
  intros napp. destruct t => //.
Qed.

Lemma head_mkApps_nApp f a : ~~ EAst.isApp f -> head (EAst.mkApps f a) = f.
Proof.
  rewrite head_mkApps /head => appf.
  rewrite (decompose_app_mkApps f []) //.
Qed.

Lemma mkApps_eq_inj {t t' l l'} :
  mkApps t l = mkApps t' l' ->
  ~~ isApp t -> ~~ isApp t' -> t = t' /\ l = l'.
Proof.
  intros Happ Ht Ht'. eapply (f_equal decompose_app) in Happ. unfold decompose_app in Happ.
  rewrite !decompose_app_rec_mkApps in Happ. rewrite !nApp_decompose_app in Happ; auto.
  rewrite !app_nil_r in Happ. intuition congruence.
Qed.

Lemma mkApps_head_inj {f l f' l'} : mkApps (head f) l = mkApps (head f') l' -> head f = head f' /\ l = l'.
Proof.
  intros H; apply mkApps_eq_inj => //.
Qed.

Lemma mkApps_eq_right t l l' : mkApps t l = mkApps t l' -> l = l'.
Proof.
  rewrite mkApps_head_spine_decompose (mkApps_head_spine_decompose t l').
  move/mkApps_head_inj => [] _ eqapp.
  now eapply app_inv_head in eqapp.
Qed.

Inductive mkApps_spec : term -> list term -> term -> list term -> term -> Type :=
| mkApps_intro f l n :
    ~~ isApp f ->
    mkApps_spec f l (mkApps f (firstn n l)) (skipn n l) (mkApps f l).

Lemma decompose_app_rec_eq f l :
  ~~ isApp f ->
  decompose_app_rec f l = (f, l).
Proof.
  destruct f; simpl; try discriminate; congruence.
Qed.

Lemma decompose_app_rec_inv' f l hd args :
  decompose_app_rec f l = (hd, args) ->
  ∑ n, ~~ isApp hd /\ l = skipn n args /\ f = mkApps hd (firstn n args).
Proof.
  destruct (isApp f) eqn:Heq.
  revert l args hd.
  induction f; try discriminate. intros.
  simpl in H.
  destruct (isApp f1) eqn:Hf1.
  2:{ rewrite decompose_app_rec_eq in H => //. now apply negbT.
      revert Hf1.
      inv H. exists 1. simpl. intuition auto. now eapply negbT. }
  destruct (IHf1 eq_refl _ _ _ H).
  clear IHf1.
  exists (S x); intuition auto. eapply (f_equal (skipn 1)) in H2.
  rewrite [l]H2. now rewrite skipn_skipn Nat.add_1_r.
  rewrite -Nat.add_1_r firstn_add H3 -H2.
  now rewrite -[tApp _ _](mkApps_app hd _ [f2]).
  rewrite decompose_app_rec_eq; auto. now apply negbT.
  move=> [] H ->. subst f. exists 0. intuition auto.
  now apply negbT.
Qed.

Lemma mkApps_elim_rec t l l' :
  let app' := decompose_app_rec (mkApps t l) l' in
  mkApps_spec app'.1 app'.2 t (l ++ l') (mkApps t (l ++ l')).
Proof.
  destruct app' as [hd args] eqn:Heq.
  subst app'.
  rewrite decompose_app_rec_mkApps in Heq.
  have H := decompose_app_rec_inv' _ _ _ _ Heq.
  destruct H. simpl. destruct a as [isapp [Hl' Hl]].
  subst t.
  have H' := mkApps_intro hd args x. rewrite Hl'.
  rewrite -mkApps_app. now rewrite firstn_skipn.
Qed.

Lemma mkApps_elim t l  :
  let app' := decompose_app (mkApps t l) in
  mkApps_spec app'.1 app'.2 t l (mkApps t l).
Proof.
  have H := @mkApps_elim_rec t l [].
  now rewrite app_nil_r in H.
Qed.

Lemma mkApps_eq f args a t : ~~ isApp f -> mkApps f args = tApp a t ->
  args <> [] /\ a = (mkApps f (remove_last args)) /\ t = last args t.
Proof.
  intros napp eq.
  destruct args using rev_case.
  * cbn in eq. destruct f => //.
  * split => //.
    rewrite mkApps_app in eq. cbn in eq. noconf eq.
    rewrite remove_last_app. split => //.
    now rewrite last_last.
Qed.

Ltac solve_discr :=
  match goal with
    H : mkApps _ _ = mkApps ?f ?l |- _ =>
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  | H : ?t = mkApps ?f ?l |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  | H : mkApps ?f ?l = ?t |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  end.

Definition isRel t :=
  match t with
  | tRel _ => true
  | _ => false
  end.

Definition isEvar t :=
  match t with
  | tEvar _ _ => true
  | _ => false
  end.

Definition isFix t :=
  match t with
  | tFix _ _ => true
  | _ => false
  end.

Definition isCoFix t :=
  match t with
  | tCoFix _ _ => true
  | _ => false
  end.

Definition isConstruct t :=
  match t with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Definition isPrim t :=
  match t with
  | tPrim _ => true
  | _ => false
  end.


Definition isBox t :=
  match t with
  | tBox => true
  | _ => false
  end.

Definition is_box c :=
  match head c with
  | tBox => true
  | _ => false
  end.

Definition isLazy c :=
  match c with
  | tLazy _ => true
  | _ => false
  end.

Definition isFixApp t := isFix (head t).
Definition isConstructApp t := isConstruct (head t).
Definition isPrimApp t := isPrim (head t).
Definition isLazyApp t := isLazy (head t).

Lemma isFixApp_mkApps f l : isFixApp (mkApps f l) = isFixApp f.
Proof. rewrite /isFixApp head_mkApps //. Qed.
Lemma isConstructApp_mkApps f l : isConstructApp (mkApps f l) = isConstructApp f.
Proof. rewrite /isConstructApp head_mkApps //. Qed.
Lemma isPrimApp_mkApps f l : isPrimApp (mkApps f l) = isPrimApp f.
Proof. rewrite /isPrimApp head_mkApps //. Qed.
Lemma isLazyApp_mkApps f l : isLazyApp (mkApps f l) = isLazyApp f.
Proof. rewrite /isLazyApp head_mkApps //. Qed.

Lemma is_box_mkApps f a : is_box (mkApps f a) = is_box f.
Proof.
  now rewrite /is_box head_mkApps.
Qed.

Lemma is_box_tApp f a : is_box (tApp f a) = is_box f.
Proof.
  now rewrite /is_box head_tApp.
Qed.

Lemma nisLambda_mkApps f args : ~~ isLambda f -> ~~ isLambda (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed.
Lemma nisFix_mkApps f args : ~~ isFix f -> ~~ isFix (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed.
Lemma nisBox_mkApps f args : ~~ isBox f -> ~~ isBox (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed.
Lemma nisPrim_mkApps f args : ~~ isPrim f -> ~~ isPrim (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed.
Lemma nisLazy_mkApps f args : ~~ isLazy f -> ~~ isLazy (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed.

Definition string_of_def {A : Set} (f : A -> string) (def : def A) :=
  "(" ^ string_of_name (dname def) ^ "," ^ f (dbody def) ^ ","
      ^ string_of_nat (rarg def) ^ ")".

Definition maybe_string_of_list {A} f (l : list A) := match l with [] => "" | _ => string_of_list f l end.

Fixpoint string_of_term (t : term) : string :=
  match t with
  | tBox => "∎"
  | tRel n => "Rel(" ^ string_of_nat n ^ ")"
  | tVar n => "Var(" ^ n ^ ")"
  | tEvar ev args => "Evar(" ^ string_of_nat ev ^ "[]" (* TODO *)  ^ ")"
  | tLambda na t => "Lambda(" ^ string_of_name na ^ "," ^ string_of_term t ^ ")"
  | tLetIn na b t => "LetIn(" ^ string_of_name na ^ "," ^ string_of_term b ^ "," ^ string_of_term t ^ ")"
  | tApp f l => "App(" ^ string_of_term f ^ "," ^ string_of_term l ^ ")"
  | tConst c => "Const(" ^ string_of_kername c ^ ")"
  | tConstruct i n args => "Construct(" ^ string_of_inductive i ^ "," ^ string_of_nat n ^ maybe_string_of_list string_of_term args ^ ")"
  | tCase (ind, i) t brs =>
    "Case(" ^ string_of_inductive ind ^ "," ^ string_of_nat i ^ "," ^ string_of_term t ^ ","
            ^ string_of_list (fun b => string_of_term (snd b)) brs ^ ")"
  | tProj p c =>
    "Proj(" ^ string_of_inductive p.(proj_ind) ^ "," ^ string_of_nat p.(proj_npars) ^ "," ^ string_of_nat p.(proj_arg) ^ ","
            ^ string_of_term c ^ ")"
  | tFix l n => "Fix(" ^ (string_of_list (string_of_def string_of_term) l) ^ "," ^ string_of_nat n ^ ")"
  | tCoFix l n => "CoFix(" ^ (string_of_list (string_of_def string_of_term) l) ^ "," ^ string_of_nat n ^ ")"
  | tPrim p => "Prim(" ^ EPrimitive.string_of_prim string_of_term p ^ ")"
  | tLazy t => "Lazy(" ^ string_of_term t ^ ")"
  | tForce t => "Force(" ^ string_of_term t ^ ")"
  end.

(** Compute all the global environment dependencies of the term *)

Section PrimDeps.
  Context (deps : term -> KernameSet.t).

  Equations prim_global_deps (p : prim_val term) : KernameSet.t :=
   | (primInt; primIntModel i) => KernameSet.empty
   | (primFloat; primFloatModel f) => KernameSet.empty
   | (primString; primStringModel s) => KernameSet.empty
   | (primArray; primArrayModel a) =>
      List.fold_left (fun acc x => KernameSet.union (deps x) acc) a.(array_value) (deps a.(array_default)).

End PrimDeps.

Fixpoint term_global_deps (t : term) :=
  match t with
  | tConst kn => KernameSet.singleton kn
  | tConstruct {| inductive_mind := kn |} _ args =>
     List.fold_left (fun acc x => KernameSet.union (term_global_deps x) acc) args
          (KernameSet.singleton kn)
  | tLambda _ x => term_global_deps x
  | tApp x y
  | tLetIn _ x y => KernameSet.union (term_global_deps x) (term_global_deps y)
  | tCase (ind, _) x brs =>
    KernameSet.union (KernameSet.singleton (inductive_mind ind))
      (List.fold_left (fun acc x => KernameSet.union (term_global_deps (snd x)) acc) brs
        (term_global_deps x))
   | tFix mfix _ | tCoFix mfix _ =>
     List.fold_left (fun acc x => KernameSet.union (term_global_deps (dbody x)) acc) mfix
      KernameSet.empty
  | tProj p c =>
    KernameSet.union (KernameSet.singleton (inductive_mind p.(proj_ind)))
      (term_global_deps c)
  | tPrim p => prim_global_deps term_global_deps p
  | tLazy t => term_global_deps t
  | tForce t => term_global_deps t
  | _ => KernameSet.empty
  end.
