(* Distributed under the terms of the MIT license. *)
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import uGraph Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICSize.

Require Import ssreflect.
From Equations Require Import Equations.
Set Equations Transparent.

Lemma eqb_annot_reflect {A} na na' : reflect (@eq_binder_annot A A na na') (eqb_binder_annot na na').
Proof.
  unfold eqb_binder_annot, eq_binder_annot.
  destruct Classes.eq_dec; constructor; auto.
Qed.

Definition string_of_aname (b : binder_annot name) :=
  string_of_name b.(binder_name).

Fixpoint string_of_term (t : term) :=
  match t with
  | tRel n => "Rel(" ^ string_of_nat n ^ ")"
  | tVar n => "Var(" ^ n ^ ")"
  | tEvar ev args => "Evar(" ^ string_of_nat ev ^ "," ^ string_of_list string_of_term args ^ ")"
  | tSort s => "Sort(" ^ string_of_sort s ^ ")"
  | tProd na b t => "Prod(" ^ string_of_aname na ^ "," ^
                            string_of_term b ^ "," ^ string_of_term t ^ ")"
  | tLambda na b t => "Lambda(" ^ string_of_aname na ^ "," ^ string_of_term b
                                ^ "," ^ string_of_term t ^ ")"
  | tLetIn na b t' t => "LetIn(" ^ string_of_aname na ^ "," ^ string_of_term b
                                 ^ "," ^ string_of_term t' ^ "," ^ string_of_term t ^ ")"
  | tApp f l => "App(" ^ string_of_term f ^ "," ^ string_of_term l ^ ")"
  | tConst c u => "Const(" ^ string_of_kername c ^ "," ^ string_of_universe_instance u ^ ")"
  | tInd i u => "Ind(" ^ string_of_inductive i ^ "," ^ string_of_universe_instance u ^ ")"
  | tConstruct i n u => "Construct(" ^ string_of_inductive i ^ "," ^ string_of_nat n ^ ","
                                    ^ string_of_universe_instance u ^ ")"
  | tCase ci p t brs =>
    "Case(" ^ string_of_case_info ci ^ "," ^ string_of_term t ^ ","
            ^ string_of_predicate string_of_term p ^ "," ^ string_of_list (string_of_branch string_of_term) brs ^ ")"
  | tProj p c =>
    "Proj(" ^ string_of_inductive p.(proj_ind) ^ "," ^ string_of_nat p.(proj_npars) ^ "," ^ string_of_nat p.(proj_arg) ^ ","
            ^ string_of_term c ^ ")"
  | tFix l n => "Fix(" ^ (string_of_list (string_of_def string_of_term) l) ^ "," ^ string_of_nat n ^ ")"
  | tCoFix l n => "CoFix(" ^ (string_of_list (string_of_def string_of_term) l) ^ "," ^ string_of_nat n ^ ")"
  | tPrim i => "Int(" ^ string_of_prim string_of_term i ^ ")"
  end.

Ltac change_Sk :=
  repeat match goal with
    | |- context [S (?x + ?y)] => progress change (S (x + y)) with (S x + y)
    | |- context [#|?l| + (?x + ?y)] => progress replace (#|l| + (x + y)) with ((#|l| + x) + y) by now rewrite Nat.add_assoc
  end.

Ltac solve_all_one :=
  try lazymatch goal with
  | H: tCasePredProp _ _ _ |- _ => destruct H as [? [? ?]]
  end;
  unfold tCaseBrsProp, tFixProp in *;
  autorewrite with map;
  rtoProp;
  try (
    apply map_predicate_eq_spec ||
    apply map_predicate_k_eq_spec ||
    apply map_predicate_id_spec ||
    apply map_predicate_k_id_spec ||
    apply map_branch_k_eq_spec ||
    apply map_branch_k_id_spec ||
    apply map_def_eq_spec ||
    apply map_def_id_spec ||
    apply map_branch_eq_spec ||
    apply map_branch_id_spec ||
    (eapply All_forallb_eq_forallb; [eassumption|]) ||
    (eapply mapi_context_eqP_test_id_spec; [eassumption|eassumption|]) ||
    (eapply mapi_context_eqP_spec; [eassumption|]) ||
    (eapply mapi_context_eqP_id_spec; [eassumption|]) ||
    (eapply onctx_test; [eassumption|eassumption|]) ||
    (eapply test_context_k_eqP_id_spec; [eassumption|eassumption|]) ||
    (eapply test_context_k_eqP_eq_spec; [eassumption|]) ||
    (eapply map_context_eq_spec; [eassumption|]));
  repeat toAll; try All_map; try close_Forall;
  change_Sk; auto with all;
  intuition eauto 4 with all.

Ltac solve_all := repeat (progress solve_all_one).
#[global] Hint Extern 10 => rewrite !map_branch_map_branch : all.
#[global] Hint Extern 10 => rewrite !map_predicate_map_predicate : all.

Lemma lookup_env_nil c s : lookup_global [] c = Some s -> False.
Proof.
  induction c; simpl; auto => //.
Qed.

Lemma lookup_env_cons {kn d Σ kn' d'} : lookup_global ((kn, d) :: Σ) kn' = Some d' ->
  (kn = kn' /\ d = d') \/ (kn <> kn' /\ lookup_global Σ kn' = Some d').
Proof.
  simpl.
  epose proof (ReflectEq.eqb_spec (A:=kername) kn' kn). simpl in H.
  elim: H. intros -> [= <-]; intuition auto.
  intros diff look. intuition auto.
Qed.

Lemma lookup_env_cons_fresh {kn d Σ kn'} :
  kn <> kn' ->
  lookup_global ((kn, d) :: Σ) kn' = lookup_global Σ kn'.
Proof.
  simpl.
  epose proof (ReflectEq.eqb_spec (A:=kername) kn' kn). simpl in H.
  elim: H. intros -> => //. auto.
Qed.

Fixpoint decompose_app_cps' (t : term) {A} (k : term -> list term -> A) :=
  match t with
  | tApp f a => decompose_app_cps' f (fun f l => k f (a :: l))
  | _ => k t []
  end.

Definition decompose_app_cps (t : term) {A} (k : term * list term -> A)
  := decompose_app_cps' t (fun f args => k (f, rev args)).

Fixpoint decompose_app_rec (t : term) l :=
  match t with
  | tApp f a => decompose_app_rec f (a :: l)
  | _ => (t, l)
  end.

Definition decompose_app t := decompose_app_rec t [].

Lemma decompose_app_cps'_rec {A} t k k' l
  : (forall f xs, k f xs = k' (f, rev xs ++ l))
    -> decompose_app_cps' t k = k' (decompose_app_rec t l) :> A.
Proof.
  revert k l; induction t; intros ?? Hk;
    cbn; rewrite ?Hk; try reflexivity; [].
  match goal with H : _ |- _ => erewrite H; [ reflexivity | ] end.
  intros; rewrite Hk rev_cons -app_assoc; cbn; reflexivity.
Qed.

Lemma decompose_app_cps_id {A} t k
  : decompose_app_cps t k = k (decompose_app t) :> A.
Proof.
  rewrite /decompose_app/decompose_app_cps.
  apply decompose_app_cps'_rec => *; rewrite app_nil_r //.
Qed.

Lemma mkApps_tApp f a l : mkApps (tApp f a) l = mkApps f (a :: l).
Proof. reflexivity. Qed.

Lemma tApp_mkApps f a : tApp f a = mkApps f [a].
Proof. reflexivity. Qed.

Definition mkApps_decompose_app_rec t l :
  mkApps t l = mkApps (fst (decompose_app_rec t l)) (snd (decompose_app_rec t l)).
Proof.
  revert l; induction t; try reflexivity.
  intro l; cbn in *.
  transitivity (mkApps t1 ((t2 ::l))). reflexivity.
  now rewrite IHt1.
Qed.

Definition mkApps_decompose_app t :
  t = mkApps (fst (decompose_app t)) (snd (decompose_app t))
  := mkApps_decompose_app_rec t [].

Lemma decompose_app_rec_mkApps f l l' : decompose_app_rec (mkApps f l) l' =
                                    decompose_app_rec f (l ++ l').
Proof.
  induction l in f, l' |- *; simpl; auto; rewrite IHl ?app_nil_r; auto.
Qed.

Require Import ssrbool.

Lemma decompose_app_mkApps f l :
  ~~ isApp f -> decompose_app (mkApps f l) = (f, l).
Proof.
  intros Hf. rewrite /decompose_app decompose_app_rec_mkApps. rewrite app_nil_r.
  destruct f; simpl in *; (discriminate || reflexivity).
Qed.

Lemma mkApps_app f l l' : mkApps f (l ++ l') = mkApps (mkApps f l) l'.
Proof.
  induction l in f, l' |- *; destruct l'; simpl; rewrite ?app_nil_r; auto.
  rewrite IHl //.
Qed.


Lemma mkApps_tApp_inj fn args t u :
  ~~ isApp fn ->
  mkApps fn args = tApp t u ->
  t = mkApps fn (removelast args) /\ u = last args t.
Proof.
  intros napp eqapp.
  destruct args using rev_case => //.
  simpl in eqapp. subst fn => //.
  rewrite mkApps_app in eqapp. noconf eqapp.
  now rewrite removelast_app // last_app // /= app_nil_r.
Qed.

Lemma removelast_length {A} (args : list A) : #|removelast args| = Nat.pred #|args|.
Proof.
  induction args => //. destruct args => //.
  now rewrite (removelast_app [_]) // app_length IHargs /=.
Qed.

Lemma nth_error_removelast {A} {args : list A} {n arg} :
  nth_error (removelast args) n = Some arg ->
  nth_error args n = Some arg.
Proof.
  intros h. rewrite nth_error_removelast //.
  apply nth_error_Some_length in h.
  now rewrite removelast_length in h.
Qed.

Lemma mkApps_discr f args t :
  args <> [] ->
  mkApps f args = t ->
  ~~ isApp t -> False.
Proof.
  intros.
  destruct args using rev_case => //.
  rewrite mkApps_app in H0. destruct t => //.
Qed.

Fixpoint decompose_prod (t : term) : (list aname) * (list term) * term :=
  match t with
  | tProd n A B => let (nAs, B) := decompose_prod B in
                  let (ns, As) := nAs in
                  (n :: ns, A :: As, B)
  | _ => ([], [], t)
  end.

Fixpoint remove_arity (n : nat) (t : term) : term :=
  match n with
  | O => t
  | S n => match t with
          | tProd _ _ B => remove_arity n B
          | _ => t (* TODO *)
          end
  end.

Definition isConstruct_app t :=
  match fst (decompose_app t) with
  | tConstruct _ _ _ => true
  | _ => false
  end.

(* was mind_decl_to_entry *)
Definition mind_body_to_entry (decl : mutual_inductive_body)
  : mutual_inductive_entry.
Proof.
  refine {| mind_entry_record := None; (* not a record *)
            mind_entry_finite := Finite; (* inductive *)
            mind_entry_params := _;
            mind_entry_inds := _;
            mind_entry_universes := decl.(ind_universes);
            mind_entry_private := None |}.
  - refine (match List.hd_error decl.(ind_bodies) with
            | Some i0 => _
            | None => nil (* assert false: at least one inductive in a mutual block *)
            end).
    pose (typ := decompose_prod i0.(ind_type)).
    destruct typ as [[names types] _].
    apply (List.firstn decl.(ind_npars)) in names.
    apply (List.firstn decl.(ind_npars)) in types.
    refine (map (fun '(x, ty) => vass x ty) (combine names types)).
  - refine (List.map _ decl.(ind_bodies)).
    intros [].
    refine {| mind_entry_typename := ind_name0;
              mind_entry_arity := remove_arity decl.(ind_npars) ind_type0;
              mind_entry_template := false;
              mind_entry_consnames := _;
              mind_entry_lc := _;
            |}.
    refine (List.map (fun x => cstr_name x) ind_ctors0).
    refine (List.map (fun x => remove_arity decl.(ind_npars)
                                                (cstr_type x)) ind_ctors0).
Defined.

Fixpoint decompose_prod_assum (Γ : context) (t : term) : context * term :=
  match t with
  | tProd n A B => decompose_prod_assum (Γ ,, vass n A) B
  | tLetIn na b bty b' => decompose_prod_assum (Γ ,, vdef na b bty) b'
  | _ => (Γ, t)
  end.

Lemma decompose_prod_assum_ctx ctx t : decompose_prod_assum ctx t =
  let (ctx', t') := decompose_prod_assum [] t in
  (ctx ,,, ctx', t').
Proof.
  induction t in ctx |- *; simpl; auto.
  - simpl. rewrite IHt2.
    rewrite (IHt2 ([] ,, vass _ _)).
    destruct (decompose_prod_assum [] t2). simpl.
    unfold snoc. now rewrite app_context_assoc.
  - simpl. rewrite IHt3.
    rewrite (IHt3 ([] ,, vdef _ _ _)).
    destruct (decompose_prod_assum [] t3). simpl.
    unfold snoc. now rewrite app_context_assoc.
Qed.

Fixpoint decompose_prod_n_assum (Γ : context) n (t : term) : option (context * term) :=
  match n with
  | 0 => Some (Γ, t)
  | S n =>
    match t with
    | tProd na A B => decompose_prod_n_assum (Γ ,, vass na A) n B
    | tLetIn na b bty b' => decompose_prod_n_assum (Γ ,, vdef na b bty) n b'
    | _ => None
    end
  end.

(* TODO move *)
Lemma it_mkLambda_or_LetIn_app l l' t :
  it_mkLambda_or_LetIn (l ++ l') t = it_mkLambda_or_LetIn l' (it_mkLambda_or_LetIn l t).
Proof. induction l in l', t |- *; simpl; auto. Qed.

Lemma decompose_prod_n_assum_it_mkProd ctx ctx' ty :
  decompose_prod_n_assum ctx #|ctx'| (it_mkProd_or_LetIn ctx' ty) = Some (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty.
  rewrite app_length /= it_mkProd_or_LetIn_app /=.
  destruct x as [na [body|] ty'] => /=;
  now rewrite !Nat.add_1_r /= IHctx' -app_assoc.
Qed.

Definition is_ind_app_head t :=
  let (f, l) := decompose_app t in
  match f with
  | tInd _ _ => true
  | _ => false
  end.

Lemma is_ind_app_head_mkApps ind u l : is_ind_app_head (mkApps (tInd ind u) l).
Proof.
  unfold is_ind_app_head.
  unfold decompose_app. rewrite decompose_app_rec_mkApps. now simpl; trivial.
Qed.

Lemma decompose_prod_assum_it_mkProd ctx ctx' ty :
  is_ind_app_head ty ->
  decompose_prod_assum ctx (it_mkProd_or_LetIn ctx' ty) = (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty /=.
  destruct ty; unfold is_ind_app_head; simpl; try (congruence || reflexivity).
  move=> Hty. rewrite it_mkProd_or_LetIn_app /=.
  case: x => [na [body|] ty'] /=; by rewrite IHctx' // /snoc -app_assoc.
Qed.

Lemma reln_length Γ Γ' n : #|reln Γ n Γ'| = #|Γ| + context_assumptions Γ'.
Proof.
  induction Γ' in n, Γ |- *; simpl; auto.
  destruct a as [? [b|] ?]; simpl; auto.
  rewrite Nat.add_1_r. simpl. rewrite IHΓ' => /= //.
Qed.

Lemma to_extended_list_k_length Γ n : #|to_extended_list_k Γ n| = context_assumptions Γ.
Proof.
  now rewrite /to_extended_list_k reln_length.
Qed.

Lemma reln_list_lift_above l p Γ :
  Forall (fun x => exists n, x = tRel n /\ p <= n /\ n < p + length Γ) l ->
  Forall (fun x => exists n, x = tRel n /\ p <= n /\ n < p + length Γ) (reln l p Γ).
Proof.
  generalize (Nat.le_refl p).
  generalize p at 1 3 5.
  induction Γ in p, l |- *. simpl. auto.
  intros. destruct a. destruct decl_body. simpl.
  assert(p0 <= S p) by lia.
  specialize (IHΓ l (S p) p0 H1). rewrite <- Nat.add_succ_comm, Nat.add_1_r.
  simpl in *. rewrite <- Nat.add_succ_comm in H0. eauto.
  simpl in *.
  specialize (IHΓ (tRel p :: l) (S p) p0 ltac:(lia)). rewrite <- Nat.add_succ_comm, Nat.add_1_r.
  eapply IHΓ. simpl in *. rewrite <- Nat.add_succ_comm in H0. auto.
  simpl in *.
  constructor. exists p. intuition lia. auto.
Qed.

Lemma to_extended_list_k_spec Γ k :
  Forall (fun x => exists n, x = tRel n /\ k <= n /\ n < k + length Γ) (to_extended_list_k Γ k).
Proof.
  pose (reln_list_lift_above [] k Γ).
  unfold to_extended_list_k.
  forward f. constructor. apply f.
Qed.

Lemma to_extended_list_lift_above Γ :
  Forall (fun x => exists n, x = tRel n /\ n < length Γ) (to_extended_list Γ).
Proof.
  pose (reln_list_lift_above [] 0 Γ).
  unfold to_extended_list.
  forward f. constructor. eapply Forall_impl; eauto. intros.
  destruct H; eexists; intuition eauto.
Qed.

Fixpoint reln_alt p (Γ : context) :=
  match Γ with
  | [] => []
  | {| decl_body := Some _ |} :: Γ => reln_alt (p + 1) Γ
  | {| decl_body := None |} :: Γ => tRel p :: reln_alt (p + 1) Γ
  end.

Lemma reln_alt_eq l Γ k : reln l k Γ = List.rev (reln_alt k Γ) ++ l.
Proof.
  induction Γ in l, k |- *; simpl; auto.
  destruct a as [na [body|] ty]; simpl.
  now rewrite IHΓ.
  now rewrite IHΓ -app_assoc.
Qed.

Lemma to_extended_list_k_cons d Γ k :
  to_extended_list_k (d :: Γ) k =
  match d.(decl_body) with
  | None => to_extended_list_k Γ (S k) ++ [tRel k]
  | Some b => to_extended_list_k Γ (S k)
  end.
Proof.
  rewrite /to_extended_list_k reln_alt_eq. simpl.
  destruct d as [na [body|] ty]. simpl.
  now rewrite reln_alt_eq Nat.add_1_r.
  simpl. rewrite reln_alt_eq.
  now rewrite -app_assoc !app_nil_r Nat.add_1_r.
Qed.

Ltac merge_All :=
  unfold tFixProp, tCaseBrsProp in *;
  repeat toAll.

#[global]
Hint Rewrite @map_def_id @map_id : map.

(* TODO move *)
Ltac close_All :=
  match goal with
  | H : Forall _ _ |- Forall _ _ => apply (Forall_impl H); clear H; simpl
  | H : All _ _ |- All _ _ => apply (All_impl H); clear H; simpl
  | H : OnOne2 _ _ _ |- OnOne2 _ _ _ => apply (OnOne2_impl H); clear H; simpl
  | H : All2 _ _ _ |- All2 _ _ _ => apply (All2_impl H); clear H; simpl
  | H : Forall2 _ _ _ |- Forall2 _ _ _ => apply (Forall2_impl H); clear H; simpl
  | H : All _ _ |- All2 _ _ _ =>
    apply (All_All2 H); clear H; simpl
  | H : All2 _ _ _ |- All _ _ =>
    (apply (All2_All_left H) || apply (All2_All_right H)); clear H; simpl
  end.

Lemma mkApps_inj :
  forall u v l,
    mkApps u l = mkApps v l ->
    u = v.
Proof.
  intros u v l eq.
  revert u v eq.
  induction l ; intros u v eq.
  - cbn in eq. assumption.
  - cbn in eq. apply IHl in eq.
    inversion eq. reflexivity.
Qed.

Lemma isApp_mkApps :
  forall u l,
    isApp u ->
    isApp (mkApps u l).
Proof.
  intros u l h.
  induction l in u, h |- *.
  - cbn. assumption.
  - cbn. apply IHl. reflexivity.
Qed.

Lemma decompose_app_rec_notApp :
  forall t l u l',
    decompose_app_rec t l = (u, l') ->
    isApp u = false.
Proof.
  intros t l u l' e.
  induction t in l, u, l', e |- *.
  all: try (cbn in e ; inversion e ; reflexivity).
  cbn in e. eapply IHt1. eassumption.
Qed.

Lemma decompose_app_notApp :
  forall t u l,
    decompose_app t = (u, l) ->
    isApp u = false.
Proof.
  intros t u l e.
  eapply decompose_app_rec_notApp. eassumption.
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

Lemma decompose_app_nonnil t f l :
  isApp t ->
  decompose_app t = (f, l) -> l <> [].
Proof.
  intros isApp.
  destruct t; simpl => //.
  intros da.
  pose proof (decompose_app_notApp _ _ _ da).
  apply decompose_app_inv in da.
  destruct l using rev_ind.
  unfold decompose_app => /=.
  destruct f => //.
  destruct l => //.
Qed.

Fixpoint nApp t :=
  match t with
  | tApp u _ => S (nApp u)
  | _ => 0
  end.

Lemma isApp_false_nApp :
  forall u,
    isApp u = false ->
    nApp u = 0.
Proof.
  intros u h.
  destruct u.
  all: try reflexivity.
  discriminate.
Qed.

Lemma nApp_mkApps :
  forall t l,
    nApp (mkApps t l) = nApp t + #|l|.
Proof.
  intros t l.
  induction l in t |- *.
  - simpl. lia.
  - simpl. rewrite IHl. cbn. lia.
Qed.

Lemma decompose_app_eq_mkApps :
  forall t u l l',
    decompose_app t = (mkApps u l', l) ->
    l' = [].
Proof.
  intros t u l l' e.
  apply decompose_app_notApp in e.
  apply isApp_false_nApp in e.
  rewrite nApp_mkApps in e.
  destruct l' ; cbn in e ; try lia.
  reflexivity.
Qed.

Lemma mkApps_nApp_inj :
  forall u u' l l',
    nApp u = nApp u' ->
    mkApps u l = mkApps u' l' ->
    u = u' /\ l = l'.
Proof.
  intros u u' l l' h e.
  induction l in u, u', l', h, e |- *.
  - cbn in e. subst.
    destruct l' ; auto.
    exfalso.
    rewrite nApp_mkApps in h. cbn in h. lia.
  - destruct l'.
    + cbn in e. subst. exfalso.
      rewrite nApp_mkApps in h. cbn in h. lia.
    + cbn in e. apply IHl in e.
      * destruct e as [e1 e2].
        inversion e1. subst. auto.
      * cbn. f_equal. auto.
Qed.

Lemma mkApps_notApp_inj :
  forall u u' l l',
    isApp u = false ->
    isApp u' = false ->
    mkApps u l = mkApps u' l' ->
    u = u' /\ l = l'.
Proof.
  intros u u' l l' h h' e.
  eapply mkApps_nApp_inj.
  - rewrite -> 2!isApp_false_nApp by assumption. reflexivity.
  - assumption.
Qed.

Definition head x := (decompose_app x).1.
Definition arguments x := (decompose_app x).2.

Lemma head_arguments x : mkApps (head x) (arguments x) = x.
Proof.
  unfold head, arguments, decompose_app.
  remember (decompose_app_rec x []).
  destruct p as [f l].
  symmetry in Heqp.
  eapply decompose_app_rec_inv in Heqp.
  now simpl in *.
Qed.

Lemma fst_decompose_app_rec t l : fst (decompose_app_rec t l) = fst (decompose_app t).
Proof.
  induction t in l |- *; simpl; auto. rewrite IHt1.
  unfold decompose_app. simpl. now rewrite (IHt1 [t2]).
Qed.

Lemma decompose_app_rec_head t l f : fst (decompose_app_rec t l) = f ->
  negb (isApp f).
Proof.
  induction t; unfold isApp; simpl; try intros [= <-]; auto.
  intros. apply IHt1. now rewrite !fst_decompose_app_rec.
Qed.

Lemma head_nApp x : negb (isApp (head x)).
Proof.
  unfold head.
  eapply decompose_app_rec_head. reflexivity.
Qed.

Lemma head_tapp t1 t2 : head (tApp t1 t2) = head t1.
Proof. rewrite /head /decompose_app /= fst_decompose_app_rec //. Qed.

Lemma mkApps_Fix_spec mfix idx args t : mkApps (tFix mfix idx) args = t ->
                                        match decompose_app t with
                                        | (tFix mfix idx, args') => args' = args
                                        | _ => False
                                        end.
Proof.
  intros H; apply (f_equal decompose_app) in H.
  rewrite decompose_app_mkApps in H. reflexivity.
  destruct t; noconf H. rewrite <- H. reflexivity.
  simpl. reflexivity.
Qed.

Lemma decompose_app_rec_tFix mfix idx args t l :
  decompose_app_rec t l = (tFix mfix idx, args) -> mkApps t l = mkApps (tFix mfix idx) args.
Proof.
  unfold decompose_app.
  revert l args.
  induction t; intros args l' H; noconf H. simpl in H.
  now specialize (IHt1 _ _ H).
  reflexivity.
Qed.

Lemma decompose_app_tFix mfix idx args t :
  decompose_app t = (tFix mfix idx, args) -> t = mkApps (tFix mfix idx) args.
Proof. apply decompose_app_rec_tFix. Qed.

Lemma mkApps_eq_head {x l} : mkApps x l = x -> l = [].
Proof.
  assert (WF : WellFounded (precompose lt PCUICSize.size))
    by apply wf_precompose, lt_wf.
  induction l. simpl. constructor.
  apply apply_noCycle_right. simpl. red. rewrite size_mkApps. simpl. lia.
Qed.

Lemma mkApps_eq_inv {x y l} : x = mkApps y l -> size y <= size x.
Proof.
  assert (WF : WellFounded (precompose lt size))
    by apply wf_precompose, lt_wf.
  induction l in x, y |- *. simpl. intros -> ; constructor.
  simpl. intros. specialize (IHl _ _ H). simpl in IHl. lia.
Qed.

Lemma mkApps_eq_left x y l : mkApps x l = mkApps y l -> x = y.
Proof.
  induction l in x, y |- *; simpl. auto.
  intros. simpl in *. specialize (IHl _ _ H). now noconf IHl.
Qed.

Lemma decompose_app_eq_right t l l' : decompose_app_rec t l = decompose_app_rec t l' -> l = l'.
Proof.
  induction t in l, l' |- *; simpl; intros [=]; auto.
  specialize (IHt1 _ _ H0). now noconf IHt1.
Qed.

Lemma mkApps_eq_right t l l' : mkApps t l = mkApps t l' -> l = l'.
Proof.
  intros. eapply (f_equal decompose_app) in H. unfold decompose_app in H.
  rewrite !decompose_app_rec_mkApps in H. apply decompose_app_eq_right in H.
  now rewrite !app_nil_r in H.
Qed.

Lemma atom_decompose_app t l : ~~ isApp t -> decompose_app_rec t l = pair t l.
Proof. destruct t; simpl; congruence. Qed.

Lemma mkApps_eq_inj {t t' l l'} :
  mkApps t l = mkApps t' l' ->
  ~~ isApp t -> ~~ isApp t' -> t = t' /\ l = l'.
Proof.
  intros Happ Ht Ht'. eapply (f_equal decompose_app) in Happ. unfold decompose_app in Happ.
  rewrite !decompose_app_rec_mkApps in Happ. rewrite !atom_decompose_app in Happ; auto.
  rewrite !app_nil_r in Happ. intuition congruence.
Qed.

Ltac solve_discr' :=
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

Lemma mkApps_eq_decompose_app {t t' l l'} :
  mkApps t l = mkApps t' l' ->
  decompose_app_rec t l = decompose_app_rec t' l'.
Proof.
  induction l in t, t', l' |- *; simpl.
  - intros ->. rewrite !decompose_app_rec_mkApps.
    now rewrite app_nil_r.
  - intros H. apply (IHl _ _ _ H).
Qed.

Lemma mkApps_eq_decompose {f args t} :
  mkApps f args = t ->
  ~~ isApp f ->
  fst (decompose_app t) = f.
Proof.
  intros H Happ; apply (f_equal decompose_app) in H.
  rewrite decompose_app_mkApps in H. auto. rewrite <- H. reflexivity.
Qed.

Ltac finish_discr :=
  repeat match goal with
         | [ H : ?x = ?x |- _ ] => clear H
         | [ H : mkApps _ _ = mkApps _ _ |- _ ] =>
           let H0 := fresh in let H1 := fresh in
                              specialize (mkApps_eq_inj H eq_refl eq_refl) as [H0 H1];
                              clear H;
                              try (congruence || (noconf H0; noconf H1))
         | [ H : mkApps _ _ = _ |- _ ] => apply mkApps_eq_head in H
         end.

Ltac prepare_discr :=
  repeat match goal with
         | [ H : mkApps ?f ?l = tApp ?y ?r |- _ ] => change (mkApps f l = mkApps y [r]) in H
         | [ H : tApp ?f ?l = mkApps ?y ?r |- _ ] => change (mkApps f [l] = mkApps y r) in H
         | [ H : mkApps ?x ?l = ?y |- _ ] =>
           match y with
           | mkApps _ _ => fail 1
           | _ => change (mkApps x l = mkApps y []) in H
           end
         | [ H : ?x = mkApps ?y ?l |- _ ] =>
           match x with
           | mkApps _ _ => fail 1
           | _ => change (mkApps x [] = mkApps y l) in H
           end
         end.


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

Lemma nisApp_mkApps {t l} : ~~ isApp (mkApps t l) -> ~~ isApp t /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (IHl _ H). discriminate.
Qed.

Lemma mkApps_nisApp {t t' l} : mkApps t l = t' -> ~~ isApp t' -> t = t' /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (IHl _ H). auto. subst. simpl in H0. discriminate.
Qed.

Lemma tApp_mkApps_inj f a f' l :
  tApp f a = mkApps f' l -> l <> [] ->
  f = mkApps f' (removelast l) /\ (a = last l a).
Proof.
  induction l in f' |- *; simpl; intros H. noconf H. intros Hf. congruence.
  intros . destruct l; simpl in *. now noconf H.
  specialize (IHl _ H). forward IHl by congruence.
  apply IHl.
Qed.

Definition application_atom t :=
  match t with
  | tVar _
  | tSort _
  | tInd _ _
  | tConstruct _ _ _
  | tLambda _ _ _ => true
  | _ => false
  end.

Lemma application_atom_mkApps {t l} : application_atom (mkApps t l) -> application_atom t /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (IHl _ H). discriminate.
Qed.

Ltac solve_discr :=
  (try (progress (prepare_discr; finish_discr; cbn [mkApps] in * )));
  (try (match goal with
        | [ H : is_true (application_atom _) |- _ ] => discriminate
        | [ H : is_true (application_atom (mkApps _ _)) |- _ ] =>
          destruct (application_atom_mkApps H); subst; try discriminate
        end)).

(** Use a coercion for this common projection of the global context. *)
Definition fst_ctx : global_env_ext -> global_env := fst.
Coercion fst_ctx : global_env_ext >-> global_env.

Definition empty_ext (Σ : global_env) : global_env_ext
  := (Σ, Monomorphic_ctx).


Lemma destArity_app_aux {Γ Γ' t}
  : destArity (Γ ,,, Γ') t = option_map (fun '(ctx, s) => (Γ ,,, ctx, s))
                                        (destArity Γ' t).
Proof.
  revert Γ'.
  induction t; cbn; intro Γ'; try reflexivity.
  - rewrite <- app_context_cons. now eapply IHt2.
  - rewrite <- app_context_cons. now eapply IHt3.
Qed.

Lemma destArity_app {Γ t}
  : destArity Γ t = option_map (fun '(ctx, s) => (Γ ,,, ctx, s))
                               (destArity [] t).
Proof.
  exact (@destArity_app_aux Γ [] t).
Qed.

Lemma destArity_app_Some {Γ t ctx s}
  : destArity Γ t = Some (ctx, s)
    -> ∑ ctx', destArity [] t = Some (ctx', s) /\ ctx = Γ ,,, ctx'.
Proof.
  intros H. rewrite destArity_app in H.
  destruct (destArity [] t) as [[ctx' s']|]; cbn in *.
  exists ctx'. inversion H. now subst.
  discriminate H.
Qed.

Lemma destArity_it_mkProd_or_LetIn ctx ctx' t :
  destArity ctx (it_mkProd_or_LetIn ctx' t) =
  destArity (ctx ,,, ctx') t.
Proof.
  induction ctx' in ctx, t |- *; simpl; auto.
  rewrite IHctx'. destruct a as [na [b|] ty]; reflexivity.
Qed.

Lemma mkApps_nonempty f l :
  l <> [] -> mkApps f l = tApp (mkApps f (removelast l)) (last l f).
Proof.
  destruct l using rev_ind. intros; congruence.
  intros. rewrite mkApps_app. simpl. f_equal.
  rewrite removelast_app. congruence. simpl. now rewrite app_nil_r.
  rewrite last_app. congruence.
  reflexivity.
Qed.

Lemma destArity_tFix {mfix idx args} :
  destArity [] (mkApps (tFix mfix idx) args) = None.
Proof.
  induction args. reflexivity.
  rewrite mkApps_nonempty.
  intros e; discriminate e.
  reflexivity.
Qed.

Lemma destArity_tApp {t u l} :
  destArity [] (mkApps (tApp t u) l) = None.
Proof.
  induction l. reflexivity.
  rewrite mkApps_nonempty.
  intros e; discriminate e.
  reflexivity.
Qed.

Lemma destArity_tInd {t u l} :
  destArity [] (mkApps (tInd t u) l) = None.
Proof.
  induction l. reflexivity.
  rewrite mkApps_nonempty.
  intros e; discriminate e.
  reflexivity.
Qed.

Lemma destArity_mkApps_None ctx t l :
  destArity ctx t = None -> destArity ctx (mkApps t l) = None.
Proof.
  induction l in t |- *. trivial.
  intros H. cbn. apply IHl. reflexivity.
Qed.

Lemma destArity_mkApps_Ind ctx ind u l :
  destArity ctx (mkApps (tInd ind u) l) = None.
Proof.
  apply destArity_mkApps_None. reflexivity.
Qed.

(* Helper for nested recursive functions on well-typed terms *)

Section MapInP.
  Context {A B : Type}.
  Context {P : A -> Type}.
  Context (f : forall (x : A), P x -> B).

  Equations map_InP (l : list A) (H : forall x, In x l -> P x) : list B :=
  map_InP nil _ := nil;
  map_InP (cons x xs) H := cons (f x (H x (or_introl eq_refl))) (map_InP xs (fun x inx => H x _)).
End MapInP.

Lemma map_InP_spec {A B : Type} {P : A -> Type} (f : A -> B) (l : list A) (H : forall x, In x l -> P x) :
  map_InP (fun (x : A) (_ : P x) => f x) l H = List.map f l.
Proof.
  remember (fun (x : A) (_ : P x) => f x) as g.
  funelim (map_InP g l H) => //; simpl. f_equal.
  now rewrite H0.
Qed.

Lemma nth_error_map_InP {A B : Type} {P : A -> Type} (f : forall x : A, P x -> B) (l : list A) (H : forall x, In x l -> P x) n x :
  nth_error (map_InP f l H) n = Some x ->
  ∑ a, (nth_error l n = Some a) *
  ∑ p : P a, x = f a p.
Proof.
  induction l in n, H |- *. simpl. rewrite nth_error_nil => //.
  destruct n; simpl; intros [=].
  subst x.
  eexists; intuition eauto.
  eapply IHl. eapply H1.
Qed.

Lemma map_InP_length {A B : Type} {P : A -> Type} (f : forall x : A, P x -> B) (l : list A) (H : forall x, In x l -> P x) :
  #|map_InP f l H| = #|l|.
Proof.
  induction l; simpl; auto.
Qed.
#[global]
Hint Rewrite @map_InP_length : len.

(** Views *)

Definition isSort T :=
  match T with
  | tSort u => true
  | _ => false
  end.

Inductive view_sort : term -> Type :=
| view_sort_sort s : view_sort (tSort s)
| view_sort_other t : ~ isSort t -> view_sort t.

Equations view_sortc (t : term) : view_sort t :=
  view_sortc (tSort s) := view_sort_sort s;
  view_sortc t := view_sort_other t _.

Definition isProd t :=
  match t with
  | tProd na A B => true
  | _ => false
  end.

Inductive view_prod : term -> Type :=
| view_prod_prod na A b : view_prod (tProd na A b)
| view_prod_other t : ~ isProd t -> view_prod t.

Equations view_prodc (t : term) : view_prod t :=
  view_prodc (tProd na A b) := view_prod_prod na A b;
  view_prodc t := view_prod_other t _.

Definition isInd (t : term) : bool :=
  match t with
  | tInd _ _ => true
  | _ => false
  end.

Inductive view_ind : term -> Type :=
| view_ind_tInd ind u : view_ind (tInd ind u)
| view_ind_other t : negb (isInd t) -> view_ind t.

Equations view_indc (t : term) : view_ind t :=
  view_indc (tInd ind u) => view_ind_tInd ind u;
  view_indc t => view_ind_other t _.

Inductive view_prod_sort : term -> Type :=
| view_prod_sort_prod na A B : view_prod_sort (tProd na A B)
| view_prod_sort_sort u : view_prod_sort (tSort u)
| view_prod_sort_other t :
    ~isProd t ->
    ~isSort t ->
    view_prod_sort t.

Equations view_prod_sortc (t : term) : view_prod_sort t := {
  | tProd na A B => view_prod_sort_prod na A B;
  | tSort u => view_prod_sort_sort u;
  | t => view_prod_sort_other t _ _
  }.



Lemma nth_error_ass_subst_context s k Γ :
  (forall n d, nth_error Γ n = Some d -> decl_body d = None) ->
  forall n d, nth_error (subst_context s k Γ) n = Some d -> decl_body d = None.
Proof.
  induction Γ as [|[? [] ?] ?] in |- *; simpl; auto;
  intros; destruct n; simpl in *; rewrite ?subst_context_snoc in H0; simpl in H0.
  - noconf H0; simpl.
    specialize (H 0 _ eq_refl). simpl in H; discriminate.
  - specialize (H 0 _ eq_refl). simpl in H; discriminate.
  - noconf H0; simpl. auto.
  - eapply IHΓ; intros; eauto.
    now specialize (H (S n0) d0 H1).
Qed.

Lemma nth_error_smash_context Γ Δ :
  (forall n d, nth_error Δ n = Some d -> decl_body d = None) ->
  forall n d, nth_error (smash_context Δ Γ) n = Some d -> decl_body d = None.
Proof.
  induction Γ as [|[? [] ?] ?] in Δ |- *; simpl; auto.
  - intros. eapply (IHΓ (subst_context [t] 0 Δ)); tea.
    now apply nth_error_ass_subst_context.
  - intros. eapply IHΓ. 2:eauto.
    intros.
    pose proof (nth_error_Some_length H1). autorewrite with len in H2. simpl in H2.
    destruct (eq_dec n0 #|Δ|).
    * subst.
      rewrite nth_error_app_ge in H1; try lia.
      rewrite Nat.sub_diag /= in H1. noconf H1.
      reflexivity.
    * rewrite nth_error_app_lt in H1; try lia. eauto.
Qed.


Lemma context_assumptions_smash_context Δ Γ :
  context_assumptions (smash_context Δ Γ) =
  context_assumptions Δ + context_assumptions Γ.
Proof.
  induction Γ as [|[? [] ?] ?] in Δ |- *; simpl; auto;
  rewrite IHΓ.
  - now rewrite context_assumptions_fold.
  - rewrite context_assumptions_app /=. lia.
Qed.

Lemma context_assumptions_expand_lets_ctx Γ Δ :
  context_assumptions (expand_lets_ctx Γ Δ) = context_assumptions Δ.
Proof. now rewrite /expand_lets_ctx /expand_lets_k_ctx; len. Qed.
#[global]
Hint Rewrite context_assumptions_expand_lets_ctx : len.
