From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.
Set Keyed Unification.
Set Default Goal Selector "!".

(** * Theory of σ-calculus operations *)

Declare Scope sigma_scope.
Delimit Scope sigma_scope with sigma.
Local Open Scope sigma_scope.
Ltac sigma := autorewrite with sigma.
Tactic Notation "sigma" "in" hyp(id) := autorewrite with sigma in id.

Infix "∘i" := (fun (f g : nat -> term -> term) => fun i => f i ∘ g i) (at level 40).

Definition renamingT := nat -> nat.
Definition substitutionT := nat -> term.

Bind Scope sigma_scope with substitutionT.

#[global]
Hint Rewrite Nat.add_0_r : sigma.

Ltac nat_compare_specs :=
  match goal with
  | |- context [?x <=? ?y] =>
    destruct (Nat.leb_spec x y); try lia
  | |- context [?x <? ?y] =>
    destruct (Nat.ltb_spec x y); try lia
  end.

(* Sigma calculus *)

(** Shift a renaming [f] by [k]. *)
Definition shiftn k f :=
  fun n => if Nat.ltb n k then n else k + (f (n - k)).

Section map_predicate_shift.
  Context {T : Type}.
  Context (fn : (nat -> T) -> term -> term).
  Context (shift : nat -> (nat -> T) -> nat -> T).
  Context (finst : Instance.t -> Instance.t).
  Context (f : nat -> T).

  Definition map_predicate_shift (p : predicate term) :=
    {| pparams := map (fn f) p.(pparams);
        puinst := finst p.(puinst);
        pcontext := p.(pcontext);
        preturn := fn (shift #|p.(pcontext)| f) p.(preturn) |}.

  Lemma map_shift_pparams (p : predicate term) :
    map (fn f) (pparams p) = pparams (map_predicate_shift p).
  Proof using Type. reflexivity. Qed.

  Lemma map_shift_preturn (p : predicate term) :
    fn (shift #|p.(pcontext)| f) (preturn p) = preturn (map_predicate_shift p).
  Proof using Type. reflexivity. Qed.

  Lemma map_shift_pcontext (p : predicate term) :
    (pcontext p) =
    pcontext (map_predicate_shift p).
  Proof using Type. reflexivity. Qed.

  Lemma map_shift_puinst (p : predicate term) :
    finst (puinst p) = puinst (map_predicate_shift p).
  Proof using Type. reflexivity. Qed.

End map_predicate_shift.

Section map_branch_shift.
  Context {T : Type}.
  Context (fn : (nat -> T) -> term -> term).
  Context (shift : nat -> (nat -> T) -> nat -> T).
  Context (f : nat -> T).

  Definition map_branch_shift (b : branch term) :=
  {| bcontext := b.(bcontext);
      bbody := fn (shift #|b.(bcontext)| f) b.(bbody) |}.

  Lemma map_shift_bbody (b : branch term) :
    fn (shift #|b.(bcontext)| f) (bbody b) = bbody (map_branch_shift b).
  Proof using Type. reflexivity. Qed.

  Lemma map_shift_bcontext (b : branch term) :
    (bcontext b) = bcontext (map_branch_shift b).
  Proof using Type. reflexivity. Qed.
End map_branch_shift.

Notation map_branches_shift ren f :=
  (map (map_branch_shift ren shiftn f)).

Fixpoint rename (f : renamingT) t : term :=
  match t with
  | tRel i => tRel (f i)
  | tEvar ev args => tEvar ev (List.map (rename f) args)
  | tLambda na T M => tLambda na (rename f T) (rename (shiftn 1 f) M)
  | tApp u v => tApp (rename f u) (rename f v)
  | tProd na A B => tProd na (rename f A) (rename (shiftn 1 f) B)
  | tLetIn na b t b' => tLetIn na (rename f b) (rename f t) (rename (shiftn 1 f) b')
  | tCase ind p c brs =>
    let p' := map_predicate_shift rename shiftn id f p in
    let brs' := map_branches_shift rename f brs in
    tCase ind p' (rename f c) brs'
  | tProj p c => tProj p (rename f c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
    tCoFix mfix' idx
  | tPrim p => tPrim (map_prim (rename f) p)
  | x => x
  end.

Notation rename_predicate := (map_predicate_shift rename shiftn id).
Notation rename_branches f := (map_branches_shift rename f).
Definition rename_context f (Γ : context) : context :=
  fold_context_k (fun i => rename (shiftn i f)) Γ.
Definition rename_decl f d := map_decl (rename f) d.
Definition rename_telescope r Γ :=
  mapi (fun i => map_decl (rename (shiftn i r))) Γ.

Lemma shiftn_ext n f f' : (forall i, f i = f' i) -> forall t, shiftn n f t = shiftn n f' t.
Proof.
  intros.
  unfold shiftn. destruct Nat.ltb; congruence.
Qed.

#[global]
Instance shiftn_proper : Proper (Logic.eq ==> `≐1` ==> `≐1`) shiftn.
Proof.
  intros x y -> f g Hfg ?. now apply shiftn_ext.
Qed.

Lemma shiftn_id i : shiftn i id ≐1 id.
Proof.
  intros k; rewrite /shiftn. nat_compare_specs => /= //.
  rewrite /id. lia.
Qed.

Lemma map_predicate_shift_eq_spec {T T'} fn fn' shift shift'
  finst finst' (f : nat -> T) (f' : nat -> T') (p : predicate term) :
  finst (puinst p) = finst' (puinst p) ->
  map (fn f) (pparams p) = map (fn' f') (pparams p) ->
  fn (shift #|pcontext p| f) (preturn p) = fn' (shift' #|pcontext p| f') (preturn p) ->
  map_predicate_shift fn shift finst f p = map_predicate_shift fn' shift' finst' f' p.
Proof.
  intros. unfold map_predicate_shift; f_equal; auto.
Qed.
#[global] Hint Resolve map_predicate_shift_eq_spec : all.

Lemma map_branch_shift_eq_spec {T T'} (fn : (nat -> T) -> term -> term)
  (fn' : (nat -> T') -> term -> term)
  shift shift' (f : nat -> T) (g : nat -> T') (x : branch term) :
  fn (shift #|x.(bcontext)| f) (bbody x) = fn' (shift' #|x.(bcontext)| g) (bbody x) ->
  map_branch_shift fn shift f x = map_branch_shift fn' shift' g x.
Proof.
  intros. unfold map_branch_shift; f_equal; auto.
Qed.
#[global] Hint Resolve map_branch_shift_eq_spec : all.

Lemma map_predicate_shift_id_spec {T} {fn shift} {finst} {f : nat -> T} (p : predicate term) :
  finst (puinst p) = puinst p ->
  map (fn f) (pparams p) = (pparams p) ->
  fn (shift #|pcontext p| f) (preturn p) = (preturn p) ->
  map_predicate_shift fn shift finst f p = p.
Proof.
  intros. unfold map_predicate_shift; destruct p; f_equal; auto.
Qed.
#[global] Hint Resolve map_predicate_shift_id_spec : all.

Lemma map_branch_shift_id_spec {T} {fn : (nat -> T) -> term -> term} {shift} {f : nat -> T} (x : branch term) :
  fn (shift #|x.(bcontext)| f) (bbody x) = bbody x ->
  map_branch_shift fn shift f x = x.
Proof.
  intros. unfold map_branch_shift; destruct x; simpl; f_equal; auto.
Qed.
#[global] Hint Resolve map_branch_shift_id_spec : all.

Lemma rename_ext f f' : (f ≐1 f') -> (rename f ≐1 rename f').
Proof.
  unfold pointwise_relation.
  intros H t. revert f f' H.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all; eauto using shiftn_ext].
  - f_equal; solve_all.
    * eapply map_predicate_shift_eq_spec; solve_all; eauto using shiftn_ext.
    * apply map_branch_shift_eq_spec; solve_all; eauto using shiftn_ext.
Qed.

Notation rename_branch := (map_branch_shift rename shiftn).

#[global]
Instance rename_proper : Proper (`≐1` ==> Logic.eq ==> Logic.eq) rename.
Proof. intros f f' Hff' t t' ->. now apply rename_ext. Qed.

#[global]
Instance rename_proper_pointwise : Proper (`≐1` ==> pointwise_relation _ Logic.eq) rename.
Proof. intros f f' Hff' t. now apply rename_ext. Qed.

Lemma map_predicate_shift_proper {T} (fn : (nat -> T) -> term -> term) shift :
  Proper (`≐1` ==> `≐1`) fn ->
  Proper (Logic.eq ==> `≐1` ==> `≐1`) shift ->
  Proper (`≐1` ==> `≐1` ==> `≐1`) (map_predicate_shift fn shift).
Proof.
  intros Hfn Hshift finst finst' Hfinst f g Hfg p.
  apply map_predicate_shift_eq_spec.
  * apply Hfinst.
  * now rewrite Hfg.
  * now setoid_rewrite Hfg.
Qed.

#[global]
Instance rename_predicate_proper : Proper (`≐1` ==> `≐1`) rename_predicate.
Proof.
  apply map_predicate_shift_proper; try tc.
  now intros x.
Qed.

Lemma map_branch_shift_proper {T} (fn : (nat -> T) -> term -> term) shift :
  Proper (`≐1` ==> `≐1`) fn ->
  Proper (Logic.eq ==> `≐1` ==> `≐1`) shift ->
  Proper (`≐1` ==> `≐1`) (map_branch_shift fn shift).
Proof.
  intros Hfn Hshift f g Hfg x.
  apply map_branch_shift_eq_spec.
  * now setoid_rewrite Hfg.
Qed.

#[global]
Instance rename_branch_proper : Proper (`≐1` ==> `≐1`) rename_branch.
Proof.
  apply map_branch_shift_proper; tc.
Qed.

Lemma shiftn0 r : shiftn 0 r ≐1 r.
Proof.
  intros x.
  unfold shiftn. destruct (Nat.ltb_spec x 0); try lia.
  rewrite Nat.sub_0_r. lia.
Qed.

Lemma shiftnS n r : shiftn (S n) r ≐1 shiftn 1 (shiftn n r).
Proof.
  intros x. unfold shiftn.
  destruct x.
  - simpl. auto.
  - simpl. rewrite Nat.sub_0_r.
    destruct (Nat.ltb_spec x n);
    destruct (Nat.ltb_spec (S x) (S n)); auto; lia.
Qed.

Lemma shiftn_add n m f : shiftn n (shiftn m f) ≐1 shiftn (n + m) f.
Proof.
  intros i.
  unfold shiftn.
  destruct (Nat.ltb_spec i n).
  - destruct (Nat.ltb_spec i (n + m)); try lia.
  - destruct (Nat.ltb_spec i (n + m)); try lia;
    destruct (Nat.ltb_spec (i - n) m); try lia.
    rewrite Nat.add_assoc. f_equal. f_equal. lia.
Qed.

#[global]
Hint Rewrite shiftn0 : sigma.

Definition rshiftk n := Nat.add n.

#[global]
Instance rshiftk_proper : Proper (Logic.eq ==> Logic.eq) rshiftk.
Proof.
  now intros x y ->.
Qed.

Lemma shiftn_rshiftk n f : shiftn n f ∘ rshiftk n ≐1 rshiftk n ∘ f.
Proof.
  intros i. rewrite /shiftn /rshiftk /=. nat_compare_specs.
  now replace (n + i - n) with i by lia.
Qed.
#[global]
Hint Rewrite shiftn_rshiftk : sigma.

Lemma shiftn_1_S f x : shiftn 1 f (S x) = rshiftk 1 (f x).
Proof. now rewrite /shiftn /= Nat.sub_0_r. Qed.
#[global]
Hint Rewrite shiftn_1_S : sigma.

Definition lift_renaming n k :=
  fun i =>
    if Nat.leb k i then (* Lifted *) n + i
    else i.

Lemma lift_renaming_spec n k : lift_renaming n k ≐1 (shiftn k (rshiftk n)).
Proof.
  rewrite /lift_renaming /shiftn /rshiftk.
  intros i. repeat nat_compare_specs.
Qed.

Lemma lift_renaming_0_rshift k : lift_renaming k 0 ≐1 rshiftk k.
Proof. reflexivity. Qed.

Lemma shiftn_lift_renaming n m k :
  shiftn m (lift_renaming n k) ≐1 lift_renaming n (m + k).
Proof.
  now rewrite !lift_renaming_spec shiftn_add.
Qed.

Lemma lift_rename n k t : lift n k t = rename (lift_renaming n k) t.
Proof.
  revert n k.
  elim t using term_forall_list_ind; simpl in |- *; intros; try reflexivity;
    try (rewrite ?H ?H0 ?H1; reflexivity);
    try solve [f_equal; solve_all].
  - f_equal; eauto.
    now rewrite H0 shiftn_lift_renaming.
  - f_equal; eauto.
    now rewrite H0 shiftn_lift_renaming.
  - f_equal; eauto.
    rewrite H1. now rewrite shiftn_lift_renaming.
  - f_equal; auto.
    * solve_all.
      unfold map_predicate_k, rename_predicate; f_equal; eauto; solve_all.
      + unfold shiftf. now rewrite shiftn_lift_renaming.
    * solve_all.
      unfold map_branch_k, map_branch_shift; f_equal; eauto; solve_all.
      + unfold shiftf. now rewrite shiftn_lift_renaming.
  - f_equal; auto.
    red in X. solve_all.
    rewrite b. now rewrite shiftn_lift_renaming.
  - f_equal; auto.
    red in X. solve_all.
    rewrite b. now rewrite shiftn_lift_renaming.
Qed.
#[global]
Hint Rewrite @lift_rename : sigma.

Lemma lift0_rename k : lift0 k ≐1 rename (rshiftk k).
Proof.
  now intros t; rewrite lift_rename lift_renaming_0_rshift.
Qed.
#[global]
Hint Rewrite lift0_rename : sigma.

Definition up k (s : substitutionT) :=
  fun i =>
    if k <=? i then rename (Nat.add k) (s (i - k))
    else tRel i.

Lemma shiftn_compose n f f' : shiftn n f ∘ shiftn n f' ≐1 shiftn n (f ∘ f').
Proof.
  unfold shiftn. intros x.
  elim (Nat.ltb_spec x n) => H.
  - now rewrite (proj2 (Nat.ltb_lt x n)).
  - destruct (Nat.ltb_spec (n + f' (x - n)) n).
    * lia.
    * assert (n + f' (x - n) - n = f' (x - n)) as ->; lia.
Qed.

(* Lemma map_branches_shiftn (fn : (renamingT) -> term -> term) f f' l :
  map_branches_shift fn f (map_branches_shift fn f' l) =
  List.map (fun i => map_branch (fn (shiftn #|bcontext i| f) ∘ (fn (shiftn #|bcontext i| f'))) i) l.
Proof.
  rewrite map_map_compose. apply map_ext => i.
  rewrite map_branch_shift_map_branch_shift.
  simpl. now apply map_branch_eq_spec.
Qed. *)

Lemma mapi_context_compose f f' :
  mapi_context f ∘ mapi_context f' ≐1
  mapi_context (f ∘i f').
Proof.
  intros x.
  now rewrite !mapi_context_fold fold_context_k_compose - !mapi_context_fold.
Qed.
#[global]
Hint Rewrite mapi_context_compose : map.

Lemma rename_compose f f' : rename f ∘ rename f' ≐1 rename (f ∘ f').
Proof.
  intros x.
  induction x in f, f' |- * using term_forall_list_ind; simpl;
    f_equal;
    auto; solve_all;
    try match goal with
    [ H : forall f f', rename f (rename f' ?x) = _ |- rename _ (rename _ ?x) = _] =>
      now rewrite H shiftn_compose
    end.

  - rewrite /map_predicate_shift /= map_map.
    solve_all; len. rewrite e. f_equal; solve_all.
    * apply rename_ext, shiftn_compose.
  - rewrite /map_branch_shift /=. f_equal; solve_all.
    * len. rewrite b. apply rename_ext, shiftn_compose.
Qed.

Lemma map_predicate_shift_map_predicate_shift
      {T} {fn : (nat -> T) -> term -> term}
      {shift : nat -> (nat -> T) -> nat -> T}
      {finst finst'}
      {f f' : nat -> T}
      {p : predicate term}
      (compose : (nat -> T) -> (nat -> T) -> nat -> T) :
  forall (shiftn0 : forall f, shift 0 f ≐1 f),
  Proper (`≐1` ==> eq ==> eq) fn ->
  (forall i, fn (shift i f) ∘ fn (shift i f') ≐1 fn (shift i (compose f f'))) ->
  map_predicate_shift fn shift finst f (map_predicate_shift fn shift finst' f' p) =
  map_predicate_shift fn shift (finst ∘ finst') (compose f f') p.
Proof.
  intros shift0 Hfn Hff'.
  unfold map_predicate_shift; destruct p; cbn.
  f_equal.
  * rewrite map_map.
    specialize (Hff' 0).
    apply map_ext => x.
    specialize (Hff' x). simpl in Hff'.
    now setoid_rewrite shift0 in Hff'.
  * len. apply Hff'.
Qed.

Lemma map_predicate_shift_map_predicate
      {T} {fn : (nat -> T) -> term -> term}
      {shift : nat -> (nat -> T) -> nat -> T}
      {finst finst' f'}
      {f : nat -> T}
      {p : predicate term}
      (compose : (nat -> T) -> (term -> term) -> (nat -> T))
      :
  Proper (`≐1` ==> `≐1`) fn ->
  (map (fn f ∘ f') p.(pparams) = map (fn (compose f f')) p.(pparams)) ->
  mapi_context (fun (k : nat) (x : term) => fn (shift k f) (f' x)) p.(pcontext) =
  mapi_context (fun k : nat => fn (shift k (compose f f'))) p.(pcontext) ->
  fn (shift #|p.(pcontext)| f) (f' p.(preturn)) = fn (shift #|p.(pcontext)| (compose f f')) p.(preturn) ->
  map_predicate_shift fn shift finst f (map_predicate finst' f' f' id p) =
  map_predicate_shift fn shift (finst ∘ finst') (compose f f') p.
Proof.
  intros Hfn Hf Hf' Hf''. unfold map_predicate_shift; destruct p; cbn.
  f_equal.
  * rewrite map_map.
    now rewrite Hf.
  * len. apply Hf''.
Qed.

Lemma map_predicate_shift_map_predicate_gen
      {T} {fn : (nat -> T) -> term -> term}
      {T'} {fn' : (nat -> T') -> term -> term}
      {shift : nat -> (nat -> T) -> nat -> T}
      {shift' : nat -> (nat -> T') -> nat -> T'}
      {finst finst' f'}
      {f : nat -> T}
      {p : predicate term}
      (compose : (nat -> T) -> (term -> term) -> (nat -> T'))
      :
  Proper (`≐1` ==> `≐1`) fn ->
  (map (fn f ∘ f') p.(pparams) = map (fn' (compose f f')) p.(pparams)) ->
  mapi_context (fun (k : nat) (x : term) => fn (shift k f) (f' x)) p.(pcontext) =
  mapi_context (fun k : nat => fn' (shift' k (compose f f'))) p.(pcontext) ->
  fn (shift #|p.(pcontext)| f) (f' p.(preturn)) = fn' (shift' #|p.(pcontext)| (compose f f')) p.(preturn) ->
  map_predicate_shift fn shift finst f (map_predicate finst' f' f' id p) =
  map_predicate_shift fn' shift' (finst ∘ finst') (compose f f') p.
Proof.
  intros Hfn Hf Hf' Hf''. unfold map_predicate_shift; destruct p; cbn.
  f_equal.
  * rewrite map_map.
    now rewrite Hf.
  * len. apply Hf''.
Qed.

Lemma map_predicate_map_predicate_shift
      {T} {fn : (nat -> T) -> term -> term}
      {shift : nat -> (nat -> T) -> nat -> T}
      {finst finst' f'}
      {f : nat -> T}
      {p : predicate term}
      (compose : (term -> term) ->  (nat -> T) -> (nat -> T))
      :
  Proper (`≐1` ==> `≐1`) fn ->
  (forall f, f' ∘ fn f ≐1 fn (compose f' f)) ->
  (forall k, compose f' (shift k f) ≐1 shift k (compose f' f)) ->
  map_predicate finst' f' f' id (map_predicate_shift fn shift finst f p) =
  map_predicate_shift fn shift (finst' ∘ finst) (compose f' f) p.
Proof.
  intros Hfn Hf Hcom. unfold map_predicate_shift, map_predicate; destruct p; cbn.
  f_equal.
  * rewrite map_map.
    now rewrite Hf.
  * len. rewrite (Hf _ _).
    now setoid_rewrite Hcom.
Qed.

Lemma rename_predicate_rename_predicate (f f' : renamingT) (p : predicate term) :
  rename_predicate f (rename_predicate f' p) =
  rename_predicate (f ∘ f') p.
Proof.
  rewrite (map_predicate_shift_map_predicate_shift Basics.compose) //.
  * apply shiftn0.
  * intros i x. now rewrite (rename_compose _ _ x) shiftn_compose.
Qed.
#[global]
Hint Rewrite rename_predicate_rename_predicate : map.

Lemma map_branch_shift_map_branch_shift {T}
  {fn : (nat -> T) -> term -> term}
  {shift : nat -> (nat -> T) -> nat -> T}
  {f f' : nat -> T} {b : branch term}
  (compose : (nat -> T) -> (nat -> T) -> nat -> T) :
  (forall i, fn (shift i f) ∘ fn (shift i f') ≐1 fn (shift i (compose f f'))) ->
  map_branch_shift fn shift f (map_branch_shift fn shift f' b) =
  map_branch_shift fn shift (compose f f') b.
Proof.
  intros Hfn.
  unfold map_branch_shift; destruct b; cbn.
  f_equal.
  * len. apply Hfn.
Qed.

Lemma rename_branch_rename_branch f f' :
  rename_branch f ∘ rename_branch f' ≐1
  rename_branch (f ∘ f').
Proof.
  intros br.
  rewrite (map_branch_shift_map_branch_shift Basics.compose) //.
  intros i x. now rewrite (rename_compose _ _ x) shiftn_compose.
Qed.
#[global]
Hint Rewrite rename_branch_rename_branch : map.

Lemma rename_branches_rename_branches f f' :
  rename_branches f ∘ rename_branches f' ≐1
  rename_branches (f ∘ f').
Proof.
  intros br.
  now autorewrite with map.
Qed.
#[global]
Hint Rewrite rename_branches_rename_branches : map.

Lemma rename_shiftn :
  forall f k t,
    rename (shiftn k f) (lift0 k t) = lift0 k (rename f t).
Proof.
  intros f k t.
  rewrite lift0_rename !(rename_compose _ _ _).
  now sigma.
Qed.

Lemma up_up k k' s : up k (up k' s) ≐1 up (k + k') s.
Proof.
  red. intros x. unfold up.
  elim (Nat.leb_spec k x) => H.
  - elim (Nat.leb_spec (k + k') x) => H'.
    + elim (Nat.leb_spec k' (x - k)) => H''.
      ++ rewrite Nat.sub_add_distr.
         rewrite -> rename_compose. apply rename_ext => t. lia.
      ++ simpl. lia.
    + edestruct (Nat.leb_spec k' (x - k)); simpl; lia_f_equal.
  - elim (Nat.leb_spec (k + k') x) => H'; lia_f_equal.
Qed.

Fixpoint inst s u :=
  match u with
  | tRel n => s n
  | tEvar ev args => tEvar ev (List.map (inst s) args)
  | tLambda na T M => tLambda na (inst s T) (inst (up 1 s) M)
  | tApp u v => tApp (inst s u) (inst s v)
  | tProd na A B => tProd na (inst s A) (inst (up 1 s) B)
  | tLetIn na b ty b' => tLetIn na (inst s b) (inst s ty) (inst (up 1 s) b')
  | tCase ind p c brs =>
    let p' := map_predicate_shift inst up id s p in
    let brs' := map (map_branch_shift inst up s) brs in
    tCase ind p' (inst s c) brs'
  | tProj p c => tProj p (inst s c)
  | tFix mfix idx =>
    let mfix' := map (map_def (inst s) (inst (up (List.length mfix) s))) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := map (map_def (inst s) (inst (up (List.length mfix) s))) mfix in
    tCoFix mfix' idx
  | tPrim p => tPrim (map_prim (inst s) p)
  | x => x
  end.

Notation inst_predicate := (map_predicate_shift inst up id).
Notation inst_branch := (map_branch_shift inst up).
Notation inst_branches f := (map (inst_branch f)).

Definition ren_fn (l : list nat) :=
  fun i =>
    match List.nth_error l i with
    | None => (i - List.length l)
    | Some t => t
    end.

Definition subst_fn (l : list term) :=
  fun i =>
    match List.nth_error l i with
    | None => tRel (i - List.length l)
    | Some t => t
    end.

Lemma up_ext k s s' : s ≐1 s' -> up k s ≐1 up k s'.
Proof.
  unfold up. intros Hs t. elim (Nat.leb_spec k t) => H; auto.
  f_equal. apply Hs.
Qed.

#[global]
Instance up_proper : Proper (Logic.eq ==> `≐1` ==> `≐1`) up.
Proof.
  intros k y <- f g. apply up_ext.
Qed.

Lemma inst_ext s s' : s ≐1 s' -> inst s ≐1 inst s'.
Proof.
  intros Hs t. revert s s' Hs.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all; eauto using up_ext].
  - f_equal; solve_all.
    * eapply map_predicate_shift_eq_spec; solve_all; eauto using up_ext.
    * apply map_branch_shift_eq_spec; solve_all; eauto using up_ext.
Qed.

#[global]
Instance proper_inst : Proper (`≐1` ==> Logic.eq ==> Logic.eq) inst.
Proof.
  intros f f' Hff' t t' ->. now apply inst_ext.
Qed.

#[global]
Instance proper_inst' : Proper (`≐1` ==> `≐1`) inst.
Proof.
  intros f f' Hff' t. now apply inst_ext.
Qed.

#[global]
Instance up_proper' k : Proper (`≐1` ==> `≐1`) (up k).
Proof. reduce_goal. now apply up_ext. Qed.

#[global]
Instance inst_predicate_proper : Proper (`≐1` ==> `≐1`) inst_predicate.
Proof.
  apply map_predicate_shift_proper; try tc.
  now intros x.
Qed.

#[global]
Instance inst_branch_proper : Proper (`≐1` ==> `≐1`) inst_branch.
Proof.
  apply map_branch_shift_proper; try tc.
Qed.

Definition ren (f : renamingT) : substitutionT :=
  fun i => tRel (f i).

#[global]
Instance ren_ext : Morphisms.Proper (`≐1` ==> `≐1`)%signature ren.
Proof.
  reduce_goal. unfold ren. now rewrite H.
Qed.

Lemma ren_shiftn n f : up n (ren f) ≐1 ren (shiftn n f).
Proof.
  unfold ren, up, shiftn.
  intros i.
  elim (Nat.ltb_spec i n) => H; elim (Nat.leb_spec n i) => H'; try lia; trivial.
Qed.

Lemma rename_inst f : rename f ≐1 inst (ren f).
Proof.
  intros t. revert f.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal; eauto. now rewrite H0 -ren_shiftn.
  - f_equal; eauto. now rewrite H0 -ren_shiftn.
  - f_equal; eauto. now rewrite H1 -ren_shiftn.
  - f_equal; eauto; solve_all.
    * eapply map_predicate_shift_eq_spec; solve_all.
      now rewrite e ren_shiftn.
    * apply map_branch_shift_eq_spec; solve_all.
      + now rewrite b -ren_shiftn.
  - f_equal; eauto. solve_all.
    now rewrite b ren_shiftn.
  - f_equal; eauto. solve_all.
    now rewrite b ren_shiftn.
Qed.

#[global]
Hint Rewrite @rename_inst : sigma.

(** Show the σ-calculus equations.

    Additional combinators: [idsn n] for n-identity, [consn] for consing a parallel substitution.
 *)

Notation "t '.[' σ ]" := (inst σ t) (at level 6, format "t .[ σ ]") : sigma_scope.

Definition subst_cons (t : term) (f : substitutionT) :=
  fun i =>
    match i with
    | 0 => t
    | S n => f n
    end.

Notation " t ⋅ s " := (subst_cons t s) (at level 70) : sigma_scope.

#[global]
Instance subst_cons_proper : Proper (Logic.eq ==> `≐1` ==> `≐1`) subst_cons.
Proof. intros x y -> f f' Hff'. intros i. destruct i; simpl; trivial. Qed.

Definition shift : substitutionT := tRel ∘ S.
Notation "↑" := shift : sigma_scope.

Definition subst_compose (σ τ : substitutionT) :=
  fun i => (σ i).[τ].

Infix "∘s" := subst_compose (at level 40) : sigma_scope.

#[global]
Instance subst_compose_proper : Proper (`≐1` ==> `≐1` ==> `≐1`) subst_compose.
Proof.
  intros f f' Hff' g g' Hgg'. intros x. unfold subst_compose.
  now rewrite Hgg' Hff'.
Qed.

Definition Up σ : substitutionT := tRel 0 ⋅ (σ ∘s ↑).
Notation "⇑ s" := (Up s) (at level 20).

#[global]
Instance Up_ext : Proper (`≐1` ==> `≐1`) Up.
Proof.
  unfold Up. reduce_goal. unfold subst_compose, subst_cons.
  destruct a => //. now rewrite H.
Qed.

Lemma up_Up σ : up 1 σ ≐1 ⇑ σ.
Proof.
  unfold up.
  intros i.
  elim (Nat.leb_spec 1 i) => H.
  - unfold subst_cons, shift. destruct i.
    -- lia.
    -- simpl. rewrite Nat.sub_0_r.
       unfold subst_compose.
       now rewrite rename_inst.
  - red in H. destruct i; [|lia]. reflexivity.
Qed.

(** Simplify away [up 1] *)
#[global]
Hint Rewrite up_Up : sigma.

Definition ids (x : nat) := tRel x.

Definition ren_id (x : nat) := x.

Lemma ren_id_ids : ren ren_id ≐1 ids.
Proof. reflexivity. Qed.

Lemma shiftn_ren_id n : shiftn n ren_id ≐1 ren_id.
Proof. apply shiftn_id. Qed.

Lemma rename_ren_id : rename ren_id ≐1 id.
Proof.
  intros t. unfold id.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal; auto. now rewrite shiftn_id.
  - f_equal; auto. now rewrite shiftn_id.
  - f_equal; auto. now rewrite shiftn_id.
  - f_equal; solve_all.
    * eapply map_predicate_shift_id_spec; solve_all; now rewrite shiftn_id.
    * now rewrite shiftn_id.
  - f_equal; auto. solve_all.
    now rewrite shiftn_id.
  - f_equal; auto. solve_all.
    now rewrite shiftn_id.
Qed.

Lemma subst_ids t : t.[ids] = t.
Proof.
  now rewrite -ren_id_ids -rename_inst rename_ren_id.
Qed.

#[global]
Hint Rewrite subst_ids : sigma.

Lemma compose_ids_r σ : σ ∘s ids ≐1 σ.
Proof.
  unfold subst_compose. intros i; apply subst_ids.
Qed.

Lemma compose_ids_l σ : ids ∘s σ ≐1 σ.
Proof. reflexivity. Qed.

#[global]
Hint Rewrite compose_ids_r compose_ids_l : sigma.

Definition shiftk (k : nat) (x : nat) := tRel (k + x).
Notation "↑^ k" := (shiftk k) (at level 30, k at level 2, format "↑^ k") : sigma_scope.

Lemma shiftk_0 : shiftk 0 ≐1 ids.
Proof.
  intros i. reflexivity.
Qed.

Definition subst_consn {A} (l : list A) (σ : nat -> A) :=
  fun i =>
    match List.nth_error l i with
    | None => σ (i - List.length l)
    | Some t => t
    end.

Notation " t ⋅n s " := (subst_consn t s) (at level 40) : sigma_scope.

Lemma subst_consn_nil {A} (σ : nat -> A) : nil ⋅n σ ≐1 σ.
Proof.
  intros i. unfold subst_consn. rewrite nth_error_nil.
  now rewrite Nat.sub_0_r.
Qed.
#[global]
Hint Rewrite @subst_consn_nil : sigma.

Lemma subst_consn_subst_cons t l σ : (t :: l) ⋅n σ ≐1 (t ⋅ subst_consn l σ).
Proof.
  intros i. unfold subst_consn. induction i; simpl; trivial.
Qed.

Lemma subst_consn_tip t σ : [t] ⋅n σ ≐1 (t ⋅ σ).
Proof. now rewrite subst_consn_subst_cons subst_consn_nil. Qed.
#[global]
Hint Rewrite @subst_consn_tip : sigma.

#[global]
Instance subst_consn_proper {A} : Proper (Logic.eq ==> `≐1` ==> `≐1`) (@subst_consn A).
Proof.
  intros ? l -> f f' Hff' i.
  unfold subst_consn. destruct nth_error eqn:Heq; auto.
Qed.

#[global]
Instance subst_consn_proper_ext {A} : Proper (Logic.eq ==> `≐1` ==> Logic.eq ==> Logic.eq) (@subst_consn A).
Proof.
  intros ? l -> f f' Hff' i i' <-.
  unfold subst_consn. destruct nth_error eqn:Heq; auto.
Qed.

Fixpoint idsn n : list term :=
  match n with
  | 0 => []
  | S n => idsn n ++ [tRel n]
  end.

Definition subst_cons_gen {A} (t : A) (f : nat -> A) :=
  fun i =>
    match i with
    | 0 => t
    | S n => f n
    end.

#[global]
Instance subst_cons_gen_proper {A} : Proper (Logic.eq ==> `≐1` ==> `≐1`) (@subst_cons_gen A).
Proof. intros x y <- f g Hfg i. destruct i; simpl; auto. Qed.

Lemma subst_consn_subst_cons_gen {A} (t : A) l σ : subst_consn (t :: l) σ ≐1 (subst_cons_gen t (l ⋅n σ)).
Proof.
  intros i. unfold subst_consn. induction i; simpl; trivial.
Qed.

Lemma subst_consn_app {A} {l l' : list A} {σ} : (l ++ l') ⋅n σ ≐1 l ⋅n (l' ⋅n σ).
Proof.
  induction l; simpl; auto.
  - now rewrite subst_consn_nil.
  - now rewrite !subst_consn_subst_cons_gen IHl.
Qed.

Lemma subst_consn_ge {A} {l : list A} {i σ} : #|l| <= i -> (l ⋅n σ) i = σ (i - #|l|).
Proof.
  induction l in i, σ |- *; simpl.
  - now rewrite subst_consn_nil.
  - rewrite subst_consn_subst_cons_gen.
    intros H. destruct i; [lia|]. simpl.
    apply IHl. lia.
Qed.

Lemma subst_consn_lt_spec {A} {l : list A} {i} :
  i < #|l| ->
  ∑ x, (List.nth_error l i = Some x) /\ (forall σ, (l ⋅n σ) i = x)%type.
Proof.
  induction l in i |- *; simpl.
  - intros H; exfalso; lia.
  - intros H.
    destruct i.
    + simpl. exists a. split; auto.
    + specialize (IHl i). forward IHl.
      * lia.
      * destruct IHl as [x [Hnth Hsubst_cons]].
        exists x. simpl. split; auto.
Qed.

Lemma subst_consn_lt {l : list term} {i : nat} {σ} :
  i < #|l| ->
  (l ⋅n σ) i = subst_fn l i.
Proof.
  move/subst_consn_lt_spec => [x [hnth] hl].
  rewrite hl. unfold subst_fn. now rewrite hnth.
Qed.

Lemma ren_consn_lt {l : list nat} {i : nat} {σ} :
  i < #|l| ->
  (l ⋅n σ) i = ren_fn l i.
Proof.
  move/subst_consn_lt_spec => [x [hnth] hl].
  rewrite hl. unfold ren_fn. now rewrite hnth.
Qed.

Fixpoint ren_ids (n : nat) :=
  match n with
  | 0 => []
  | S n => ren_ids n ++ [n]
  end.

Lemma ren_ids_length n : #|ren_ids n| = n.
Proof. induction n; simpl; auto. rewrite length_app IHn; simpl; lia. Qed.
#[global]
Hint Rewrite ren_ids_length : len.

Lemma idsn_length n : #|idsn n| = n.
Proof.
  induction n; simpl; auto. rewrite length_app IHn; simpl; lia.
Qed.
#[global]
Hint Rewrite idsn_length : len.

Lemma idsn_lt {n i} : i < n -> nth_error (idsn n) i = Some (tRel i).
Proof.
  induction n in i |- *; simpl; auto.
  - intros H; lia.
  - intros H. destruct (Compare_dec.le_lt_dec n i).
    -- assert (n = i) by lia; subst.
       rewrite nth_error_app_ge idsn_length ?Nat.sub_diag; trea.
    -- rewrite nth_error_app_lt ?idsn_length //. apply IHn; lia.
Qed.

Lemma nth_ren_ids_lt {n i} : i < n -> nth_error (ren_ids n) i = Some i.
Proof.
  induction n in i |- *; simpl; auto.
  - intros H; lia.
  - intros H. destruct (Compare_dec.le_lt_dec n i).
    -- assert (n = i) by lia; subst.
       rewrite nth_error_app_ge ren_ids_length ?Nat.sub_diag; trea.
    -- rewrite nth_error_app_lt ?ren_ids_length //. apply IHn; lia.
Qed.

Lemma ren_ids_lt {n i} : i < n -> ren (ren_fn (ren_ids n)) i = tRel i.
Proof.
  intros lt.
  rewrite /ren /ren_fn nth_ren_ids_lt //.
Qed.

Lemma ren_idsn_consn_lt {i n : nat} {σ} : i < n ->
  ren (ren_ids n ⋅n σ) i = tRel i.
Proof.
  intros lt.
  rewrite /ren ren_consn_lt; len => //.
  rewrite /ren_fn nth_ren_ids_lt //.
Qed.

Lemma subst_ids_lt i m : i < m -> subst_fn (idsn m) i = tRel i.
Proof.
  move=> lt. rewrite /subst_fn idsn_lt //.
Qed.

Lemma subst_idsn_consn_lt {i n : nat} {σ} : i < n ->
  (idsn n ⋅n σ) i = tRel i.
Proof.
  intros lt.
  rewrite subst_consn_lt; len; try lia.
  rewrite subst_ids_lt //.
Qed.

Lemma nth_error_idsn_Some :
  forall n k,
    k < n ->
    nth_error (idsn n) k = Some (tRel k).
Proof.
  intros n k h.
  induction n in k, h |- *.
  - inversion h.
  - simpl. destruct (Nat.ltb_spec0 k n).
    + rewrite nth_error_app1.
      * rewrite idsn_length. auto.
      * eapply IHn. assumption.
    + assert (k = n) by lia. subst.
      rewrite nth_error_app2.
      * rewrite idsn_length. auto.
      * rewrite idsn_length. replace (n - n) with 0 by lia.
        simpl. reflexivity.
Qed.

Lemma nth_error_idsn_None :
  forall n k,
    k >= n ->
    nth_error (idsn n) k = None.
Proof.
  intros n k h.
  eapply nth_error_None.
  rewrite idsn_length. auto.
Qed.


Lemma subst_cons_0 t σ : (tRel 0).[t ⋅ σ] = t. Proof. reflexivity. Qed.
Lemma subst_cons_shift t σ : ↑ ∘s (t ⋅ σ) = σ. Proof. reflexivity. Qed.
#[global]
Hint Rewrite subst_cons_0 subst_cons_shift : sigma.

Lemma shiftk_shift n : ↑^(S n) ≐1 ↑^n ∘s ↑. Proof. reflexivity. Qed.

Lemma shiftk_shift_l n : ↑^(S n) ≐1 ↑ ∘s ↑^n.
Proof.
  intros i.
  unfold shiftk. unfold subst_compose, shift.
  simpl. f_equal. lia.
Qed.

Lemma subst_subst_consn s σ τ : (s ⋅ σ) ∘s τ ≐1 (s.[τ] ⋅ σ ∘s τ).
Proof.
  intros i.
  destruct i; simpl; reflexivity.
Qed.

#[global]
Hint Rewrite subst_subst_consn : sigma.

Definition Upn n σ := idsn n ⋅n (σ ∘s ↑^n).
Notation "⇑^ n σ" := (Upn n σ) (at level 30, n at level 2, format "⇑^ n  σ") : sigma_scope.

#[global]
Instance Upn_ext n : Proper (`≐1` ==> `≐1`) (Upn n).
Proof.
  unfold Upn. reduce_goal. now rewrite H.
Qed.

Lemma Upn_0 σ : ⇑^0 σ ≐1 σ.
Proof.
  unfold Upn. simpl.
  now rewrite subst_consn_nil shiftk_0 compose_ids_r.
Qed.

Lemma Upn_1_Up σ : ⇑^1 σ ≐1 ⇑ σ.
Proof.
  unfold Upn.
  intros i. destruct i; auto.
  simpl. rewrite subst_consn_ge; simpl; auto with arith.
Qed.
#[global]
Hint Rewrite Upn_1_Up : sigma.

Lemma Upn_eq n σ : Upn n σ = idsn n ⋅n (σ ∘s ↑^n).
Proof. reflexivity. Qed.

Lemma Upn_proper : Proper (Logic.eq ==> `≐1` ==> `≐1`) Upn.
Proof. intros ? ? -> f g Hfg. unfold Upn. now rewrite Hfg. Qed.

(** The σ-calculus equations for Rocq *)

Lemma inst_app {s t σ} : (tApp s t).[σ] = tApp s.[σ] t.[σ].
Proof. reflexivity. Qed.

Lemma inst_lam {na t b σ} : (tLambda na t b).[σ] = tLambda na t.[σ] b.[⇑ σ].
Proof.
  simpl. now rewrite up_Up.
Qed.

Lemma inst_prod {na t b σ} : (tProd na t b).[σ] = tProd na t.[σ] b.[⇑ σ].
Proof.
  simpl. now rewrite up_Up.
Qed.

Lemma inst_letin {na t b b' σ} : (tLetIn na t b b').[σ] = tLetIn na t.[σ] b.[σ] b'.[⇑ σ].
Proof.
  simpl. now rewrite up_Up.
Qed.

Lemma up_Upn {n σ} : up n σ ≐1 ⇑^n σ.
Proof.
  unfold up, Upn.
  intros i.
  elim (Nat.leb_spec n i) => H.
  - rewrite rename_inst.
    rewrite subst_consn_ge; rewrite idsn_length; auto.
  - assert (Hle: i < #|idsn n|) by (rewrite idsn_length; lia).
    rewrite (subst_consn_lt Hle) /subst_fn idsn_lt //.
Qed.

Lemma Upn_ren k f : ⇑^k ren f ≐1 ren (shiftn k f).
Proof.
  now rewrite -up_Upn ren_shiftn.
Qed.

Lemma inst_fix {mfix idx σ} : (tFix mfix idx).[σ] =
                              tFix (map (map_def (inst σ) (inst (⇑^#|mfix| σ))) mfix) idx.
Proof.
  simpl. f_equal. apply map_ext. intros x. apply map_def_eq_spec => //.
  now rewrite up_Upn.
Qed.

Lemma inst_cofix {mfix idx σ} : (tCoFix mfix idx).[σ] =
                                tCoFix (map (map_def (inst σ) (inst (⇑^#|mfix| σ))) mfix) idx.
Proof.
  simpl. f_equal. apply map_ext. intros x. apply map_def_eq_spec => //.
  now rewrite up_Upn.
Qed.

Lemma inst_mkApps :
  forall t l σ,
    (mkApps t l).[σ] = mkApps t.[σ] (map (inst σ) l).
Proof.
  intros t l σ.
  induction l in t, σ |- *.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

#[global]
Hint Rewrite @inst_app @inst_lam @inst_prod @inst_letin @inst_fix @inst_cofix
     @inst_mkApps : sigma.


Lemma ren_shift : ↑ ≐1 ren S.
Proof. reflexivity. Qed.

Lemma compose_ren f g : ren f ∘s ren g ≐1 ren (g ∘ f).
Proof.
  intros i.
  destruct i; simpl; reflexivity.
Qed.
#[global]
Hint Rewrite compose_ren : sigma.

Lemma subst_cons_ren i f : (tRel i ⋅ ren f) ≐1 ren (subst_cons_gen i f).
Proof.
  intros x; destruct x; auto.
Qed.

Infix "≐2" := (Logic.eq ==> (pointwise_relation _ Logic.eq))%signature (at level 70) : signature_scope.

Lemma subst_consn_subst_cons' {A} (t : A) l : (subst_consn (t :: l) ≐2 ((subst_cons_gen t) ∘ (subst_consn l)))%signature.
Proof. red.
  intros x y <-. apply subst_consn_subst_cons_gen.
Qed.

Lemma subst_consn_compose l σ' σ : l ⋅n σ' ∘s σ ≐1 (map (inst σ) l ⋅n (σ' ∘s σ)).
Proof.
  induction l; simpl.
  - now sigma.
  - rewrite subst_consn_subst_cons. sigma.
    rewrite IHl. now rewrite subst_consn_subst_cons.
Qed.

Lemma subst_consn_ids_ren n f : (idsn n ⋅n ren f) ≐1 ren (ren_ids n ⋅n f).
Proof.
  intros i.
  destruct (Nat.leb_spec n i).
  - rewrite subst_consn_ge idsn_length; auto.
    unfold ren. f_equal. rewrite subst_consn_ge ren_ids_length; auto.
  - assert (Hr:i < #|ren_ids n|) by (rewrite ren_ids_length; lia).
    assert (Hi:i < #|idsn n|) by (rewrite idsn_length; lia).
    now rewrite (subst_consn_lt Hi) subst_ids_lt // (ren_idsn_consn_lt H).
Qed.

Lemma ren_shiftk n : ren (Nat.add n) ≐1 ↑^n.
Proof. reflexivity. Qed.
#[global]
Hint Rewrite ren_shiftk : sigma.

Lemma ren_rshiftk k : ren (rshiftk k) ≐1 ↑^k.
Proof. reflexivity. Qed.
#[global]
Hint Rewrite ren_rshiftk : sigma.

Lemma map_inst_idsn σ n m : m <= n -> map (inst (⇑^n σ)) (idsn m) = idsn m.
Proof.
  induction m in n |- *; simpl; auto.
  intros.
  rewrite map_app IHm; try lia.
  f_equal. simpl. rewrite Upn_eq.
  now rewrite subst_consn_lt /subst_fn ?idsn_lt; len; try lia.
Qed.

(** Specific lemma for the fix/cofix cases where we are subst_cons'ing a list of ids in front
    of the substitution. *)
Lemma ren_subst_consn_comm:
  forall (f : renamingT) (σ : substitutionT) (n : nat),
    ren (subst_consn (ren_ids n) (rshiftk n ∘ f)) ∘s subst_consn (idsn n) (σ ∘s ↑^n) ≐1
    subst_consn (idsn n) (ren f ∘s σ ∘s ↑^n).
Proof.
  intros f σ m.
  rewrite -subst_consn_ids_ren.
  rewrite subst_consn_compose.
  apply subst_consn_proper.
  * rewrite -Upn_eq map_inst_idsn //.
  * intros i.
    rewrite /ren /subst_compose /= /rshiftk.
    rewrite subst_consn_ge; len; try lia.
    lia_f_equal.
Qed.

(** Simplify away iterated up's *)
#[global]
Hint Rewrite @up_Upn : sigma.

Lemma Upn_ren_l k f σ : ⇑^k ren f ∘s ⇑^k σ ≐1 ⇑^k (ren f ∘s σ).
Proof.
  rewrite Upn_eq.
  rewrite -(ren_shiftk k) !compose_ren !subst_consn_ids_ren.
  apply ren_subst_consn_comm.
Qed.

Lemma rename_inst_assoc t f σ : t.[ren f].[σ] = t.[ren f ∘s σ].
Proof.
  revert f σ.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal; auto. sigma.
    unfold Up.
    simpl. rewrite ren_shift. rewrite compose_ren subst_cons_ren H0.
    apply inst_ext. intros i. destruct i; auto.
  - f_equal; auto. sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H0.
    apply inst_ext. intros i. destruct i; auto.
  - f_equal; auto. sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H1.
    apply inst_ext. intros i. destruct i; auto.
  - f_equal; auto; solve_all; sigma.
    * unfold map_predicate_shift; simpl; f_equal; solve_all.
      + rewrite !up_Upn Upn_ren e -Upn_ren. len.
        now rewrite Upn_ren_l.
    * unfold map_branch_shift; simpl; f_equal; solve_all.
      + len. now rewrite !up_Upn Upn_ren b -Upn_ren Upn_ren_l.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    sigma.
    now rewrite Upn_ren b -Upn_ren Upn_ren_l.
  - f_equal; auto.
    red in X. solve_all.
    sigma.
    now rewrite Upn_ren b -Upn_ren Upn_ren_l.
Qed.

Lemma map_idsn_spec (f : term -> term) (n : nat) :
  map f (idsn n) = Nat.recursion [] (fun x l => l ++ [f (tRel x)]) n.
Proof.
  induction n; simpl.
  - reflexivity.
  - simpl. rewrite map_app. now rewrite -IHn.
Qed.

Lemma idsn_spec (n : nat) :
  idsn n = Nat.recursion [] (fun x l => l ++ [tRel x]) n.
Proof.
  induction n; simpl.
  - reflexivity.
  - simpl. now rewrite -IHn.
Qed.

Lemma nat_recursion_ext {A} (x : A) f g n :
  (forall x l', x < n -> f x l' = g x l') ->
  Nat.recursion x f n = Nat.recursion x g n.
Proof.
  intros.
  generalize (Nat.le_refl n).
  induction n at 1 3 4; simpl; auto.
  intros. simpl. rewrite IHn0; try lia. now rewrite H.
Qed.

Lemma rename_idsn_idsn m f : map (rename (ren_ids m ⋅n f)) (idsn m) = idsn m.
Proof.
  rewrite map_idsn_spec idsn_spec.
  apply nat_recursion_ext. intros x l' hx. f_equal.
  simpl. f_equal. f_equal. rewrite ren_consn_lt; len => //.
  rewrite /ren_fn. rewrite nth_ren_ids_lt //.
Qed.

Lemma inst_rename_assoc_n:
  forall (f : renamingT) (σ : substitutionT) (n : nat),
    subst_consn (idsn n) (σ ∘s ↑^n) ∘s ren (subst_consn (ren_ids n) (Init.Nat.add n ∘ f)) ≐1
    subst_consn (idsn n) (σ ∘s ren f ∘s ↑^n).
Proof.
  intros f σ m. rewrite -ren_shiftk.
  intros i.
  destruct (Nat.leb_spec m i).
  -- rewrite [subst_consn (idsn _) _ i]subst_consn_ge ?idsn_length; try lia.
     unfold subst_compose.
     rewrite [subst_consn (idsn _) _ i]subst_consn_ge ?idsn_length; try lia.
     rewrite !rename_inst_assoc !compose_ren.
     apply inst_ext. intros i'.
     unfold ren. f_equal. rewrite subst_consn_ge ?ren_ids_length; try lia.
     now assert (m + i' - m = i') as -> by lia.
  -- assert (Hr:i < #|ren_ids m |) by (rewrite ren_ids_length; lia).
     assert (Hi:i < #|idsn m |) by (rewrite idsn_length; lia).
     rewrite (subst_consn_lt Hi) subst_ids_lt //.
     rewrite subst_consn_compose.
     rewrite (subst_consn_lt); len => //.
     rewrite -rename_inst rename_idsn_idsn subst_ids_lt //.
Qed.

Lemma Upn_ren_r k f σ : ⇑^k σ ∘s ⇑^k ren f ≐1 ⇑^k (σ ∘s ren f).
Proof.
  rewrite !Upn_eq.
  rewrite -(ren_shiftk k) !compose_ren !subst_consn_ids_ren.
  apply inst_rename_assoc_n.
Qed.

Lemma inst_rename_assoc t f σ : t.[σ].[ren f] = t.[σ ∘s ren f].
Proof.
  revert f σ.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal; auto. sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H0.
    apply inst_ext. intros i. destruct i; auto. simpl.
    unfold subst_compose. simpl. now rewrite !rename_inst_assoc !compose_ren.
  - f_equal; auto. sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H0.
    apply inst_ext. intros i. destruct i; auto.
    unfold subst_compose. simpl. now rewrite !rename_inst_assoc !compose_ren.
  - f_equal; auto. sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H1.
    apply inst_ext. intros i. destruct i; auto.
    unfold subst_compose. simpl. now rewrite !rename_inst_assoc !compose_ren.
  - f_equal; auto; solve_all; sigma.
    * unfold map_predicate_shift; cbn; f_equal; solve_all.
      + now rewrite !up_Upn Upn_ren e; len; rewrite -Upn_ren Upn_ren_r.
    * sigma.
      unfold map_branch_shift; cbn; f_equal; solve_all.
      + now rewrite !up_Upn Upn_ren b; len; rewrite -Upn_ren Upn_ren_r.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    sigma. now rewrite Upn_ren b -Upn_ren Upn_ren_r.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    sigma. now rewrite Upn_ren b -Upn_ren Upn_ren_r.
Qed.

Lemma rename_subst_compose1 r s s' : ren r ∘s (s ∘s s') ≐1 ren r ∘s s ∘s s'.
Proof. unfold subst_compose. simpl. intros i. reflexivity. Qed.

Lemma rename_subst_compose2 r s s' : s ∘s (ren r ∘s s') ≐1 s ∘s ren r ∘s s'.
Proof.
  unfold subst_compose. simpl. intros i.
  rewrite rename_inst_assoc. reflexivity.
Qed.

Lemma rename_subst_compose3 r s s' : s ∘s (s' ∘s ren r) ≐1 s ∘s s' ∘s ren r.
Proof.
  unfold subst_compose. simpl. intros i.
  rewrite inst_rename_assoc. reflexivity.
Qed.

Lemma Up_Up_assoc:
  forall s s' : substitutionT, (⇑ s) ∘s (⇑ s') ≐1 ⇑ (s ∘s s').
Proof.
  intros s s'.
  unfold Up.
  rewrite ren_shift.
  rewrite subst_subst_consn.
  simpl. apply subst_cons_proper => //.
  rewrite - rename_subst_compose2.
  rewrite - rename_subst_compose3.
  now apply subst_compose_proper; auto.
Qed.

#[global]
Hint Rewrite Up_Up_assoc : sigma.

Lemma up_up_assoc:
  forall (s s' : substitutionT) (n : nat), up n s ∘s up n s' ≐1 up n (s ∘s s').
Proof.
  intros s s' n i.
  unfold up, subst_compose. simpl.
  destruct (Nat.leb_spec n i).
  - rewrite !(rename_inst (Nat.add n) (s (i - n))).
    rewrite rename_inst_assoc.
    rewrite !(rename_inst (Nat.add n) _).
    rewrite inst_rename_assoc.
    apply inst_ext.
    intros i'. unfold subst_compose.
    unfold ren. simpl.
    destruct (Nat.leb_spec n (n + i')).
    * rewrite rename_inst.
      now assert (n + i' - n = i') as -> by lia.
    * lia.
  - simpl.
    destruct (Nat.leb_spec n i); lia_f_equal.
Qed.

Lemma inst_assoc t s s' : t.[s].[s'] = t.[s ∘s s'].
Proof.
  revert s s'.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal; auto. sigma.
    now rewrite H0 Up_Up_assoc.
  - f_equal; auto. sigma.
    now rewrite H0 Up_Up_assoc.
  - f_equal; auto. sigma.
    now rewrite H1 Up_Up_assoc.
  - f_equal; auto.
    * unfold map_predicate_shift; cbn; f_equal; solve_all.
      + len. now rewrite e up_up_assoc.
    * rewrite map_map_compose; solve_all.
      unfold map_branch_shift; cbn; f_equal; solve_all.
      + len. now rewrite b up_up_assoc.
  - f_equal; auto. sigma.
    rewrite map_map_compose; solve_all.
    now rewrite b up_up_assoc.
  - f_equal; auto. sigma.
    rewrite map_map_compose; solve_all.
    now rewrite b up_up_assoc.
Qed.

#[global]
Hint Rewrite inst_assoc : sigma.

Lemma subst_compose_assoc s s' s'' : (s ∘s s') ∘s s'' ≐1 s ∘s (s' ∘s s'').
Proof.
  intros i; unfold subst_compose at 1 3 4.
  now rewrite inst_assoc.
Qed.

#[global]
Hint Rewrite subst_compose_assoc : sigma.

Lemma subst_cons_0_shift : (tRel 0 ⋅ ↑) ≐1 ids.
Proof. intros i. destruct i; reflexivity. Qed.

#[global]
Hint Rewrite subst_cons_0_shift : sigma.

Lemma subst_cons_0s_shifts σ : ((σ 0) ⋅ (↑ ∘s σ)) ≐1 σ.
Proof.
  intros i. destruct i; auto.
Qed.

#[global]
Hint Rewrite subst_cons_0s_shifts : sigma.

Lemma Upn_Up σ n : ⇑^(S n) σ ≐1 ⇑^n ⇑ σ.
Proof.
  intros i. unfold Upn.
  simpl. rewrite subst_consn_app.
  rewrite subst_consn_tip. unfold Up. apply subst_consn_proper; auto.
  rewrite shiftk_shift_l.
  intros i'. unfold subst_cons, subst_compose.
  destruct i' => //; auto; simpl.
  - unfold shiftk. now rewrite Nat.add_0_r.
  - simpl. now rewrite inst_assoc.
Qed.

Lemma Upn_1 σ : ⇑^1 σ ≐1 ⇑ σ.
Proof. now rewrite Upn_Up Upn_0. Qed.

Lemma Upn_S σ n : ⇑^(S n) σ ≐1 ⇑ ⇑^n σ.
Proof.
  rewrite Upn_Up. induction n in σ |- *.
  * rewrite !Upn_0. now eapply Up_ext.
  * rewrite Upn_Up. rewrite IHn. eapply Up_ext. now rewrite Upn_Up.
Qed.
#[global]
Hint Rewrite Upn_0 Upn_S : sigma.

(* Print Rewrite HintDb sigma. *)

Lemma subst_inst_aux s k t : subst s k t = inst (up k (subst_fn s)) t.
Proof.
  revert s k.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - unfold subst_fn, up.
    elim (Nat.leb_spec k n) => //.
    intros H.
    destruct nth_error eqn:Heq.
    * apply lift_rename.
    * simpl. eapply nth_error_None in Heq. lia_f_equal.
  - f_equal; eauto.
    rewrite H0. apply inst_ext. intros t'; now rewrite (up_up 1 k).
  - f_equal; eauto.
    rewrite H0. apply inst_ext. intros t'; now rewrite (up_up 1 k).
  - f_equal; eauto.
    rewrite H1. apply inst_ext. intros t'; now rewrite (up_up 1 k).
  - f_equal; eauto.
    * unfold map_predicate_k, map_predicate_shift; destruct p; cbn in *; f_equal; solve_all.
      + now rewrite /shiftf up_up.
    * solve_all.
      unfold map_branch_k, map_branch_shift; destruct x; cbn in *; f_equal; solve_all.
      + now rewrite /shiftf up_up.
  - f_equal; eauto; solve_all; auto.
    rewrite b. apply inst_ext. intros t'; now rewrite (up_up #|m| k).
  - f_equal; eauto.
    solve_all; auto.
    rewrite b. apply inst_ext. intros t'; now rewrite (up_up #|m| k).
Qed.

Lemma subst_fn_subst_consn s : subst_fn s ≐1 subst_consn s ids.
Proof. reflexivity. Qed.

(** substitutionT is faithfully modelled by instantiation *)
Theorem subst_inst s k t : subst s k t = inst (⇑^k (subst_consn s ids)) t.
Proof.
  rewrite subst_inst_aux up_Upn. apply inst_ext.
  unfold Upn. now rewrite subst_fn_subst_consn.
Qed.

Lemma subst0_inst (s : list term) (t : term) :
  subst0 s t = t.[s ⋅n ids].
Proof. rewrite subst_inst. now sigma. Qed.

(** Useful for point-free rewriting *)
Corollary subst_inst' s k : subst s k ≐1 inst (⇑^k (subst_consn s ids)).
Proof.
  intros t; apply subst_inst.
Qed.

Lemma map_subst_inst s k l : map (subst s k) l = map (inst (⇑^k (s ⋅n ids))) l.
Proof.
  now apply map_ext => ?; rewrite subst_inst.
Qed.

(** Simplify away [subst] to the σ-calculus [inst] primitive. *)
#[global]
Hint Rewrite @subst_inst : sigma.
#[global]
Hint Rewrite @subst_consn_nil : sigma.

#[global]
Hint Rewrite shiftk_shift_l shiftk_shift : sigma.
(* Hint Rewrite Upn_eq : sigma. *)


Fixpoint subst_app (t : term) (us : list term) : term :=
  match t, us with
  | tLambda _ A t, u :: us => subst_app (t {0 := u}) us
  | _, [] => t
  | _, _ => mkApps t us
  end.

Lemma subst_consn_shiftn n (l : list term) σ : #|l| = n -> ↑^n ∘s (l ⋅n σ) ≐1 σ.
Proof.
  induction n in l |- *; simpl; intros; sigma.
  - destruct l; try discriminate. now sigma.
  - destruct l; try discriminate. simpl in *.
    rewrite subst_consn_subst_cons.
    simpl; sigma. apply IHn. lia.
Qed.

Lemma shiftn_Upn n σ : ↑^n ∘s ⇑^n σ ≐1 σ ∘s ↑^n.
Proof.
  unfold Upn. rewrite subst_consn_shiftn //.
  now rewrite idsn_length.
Qed.
#[global]
Hint Rewrite shiftn_Upn: sigma.

Lemma id_nth_spec {A} (l : list A) :
  l = Nat.recursion [] (fun x l' =>
                          match nth_error l x with
                          | Some a => l' ++ [a]
                          | None => l'
                          end) #|l|.
Proof.
  induction l using rev_ind; simpl; try reflexivity.
  rewrite length_app. simpl. rewrite Nat.add_1_r. simpl.
  rewrite nth_error_app_ge; try lia. rewrite Nat.sub_diag. simpl.
  f_equal. rewrite {1}IHl. eapply nat_recursion_ext. intros.
  now rewrite nth_error_app_lt.
Qed.

Lemma Upn_comp n l σ : n = #|l| -> ⇑^n σ ∘s (l ⋅n ids) ≐1 l ⋅n σ.
Proof.
  intros ->. rewrite Upn_eq; simpl.
  rewrite !subst_consn_compose. sigma.
  rewrite subst_consn_shiftn ?length_map //. sigma.
  eapply subst_consn_proper; try reflexivity.
  rewrite map_idsn_spec.
  rewrite {3}(id_nth_spec l).
  eapply nat_recursion_ext. intros.
  simpl. destruct (nth_error_spec l x).
  - unfold subst_consn. rewrite e. reflexivity.
  - lia.
Qed.

Lemma shift_Up_comm σ : ↑ ∘s ⇑ σ ≐1 σ ∘s ↑.
Proof. reflexivity. Qed.

Lemma shiftk_compose n m : ↑^n ∘s ↑^m ≐1 ↑^(n + m).
Proof.
  induction n; simpl; sigma; auto.
  - reflexivity.
  - rewrite -subst_compose_assoc.
    rewrite -shiftk_shift shiftk_shift_l.
    now rewrite subst_compose_assoc IHn -shiftk_shift shiftk_shift_l.
Qed.

Lemma Upn_Upn k k' σ : ⇑^(k + k') σ ≐1 ⇑^k (⇑^k' σ).
Proof.
  setoid_rewrite <- up_Upn. rewrite -(@up_Upn k').
  symmetry; apply up_up.
Qed.
#[global]
Hint Rewrite Upn_Upn : sigma.

Lemma Upn_compose n σ σ' : ⇑^n σ ∘s ⇑^n σ' ≐1 ⇑^n (σ ∘s σ').
Proof.
  induction n.
  - unfold Upn. simpl.
    now rewrite !subst_consn_nil !shiftk_0 !compose_ids_r.
  - setoid_rewrite Upn_S. sigma. now rewrite IHn.
Qed.

Lemma up_ext_closed k' k s s' :
  (forall i, i < k' -> s i = s' i) ->
  forall i, i < k + k' ->
  up k s i = up k s' i.
Proof.
  unfold up. intros Hs t. elim (Nat.leb_spec k t) => H; auto.
  intros. f_equal. apply Hs. lia.
Qed.

Lemma subst_consn_eq s0 s1 s2 s3 x :
  x < #|s0| -> #|s0| = #|s2| ->
  subst_fn s0 x = subst_fn s2 x ->
  (s0 ⋅n s1) x = (s2 ⋅n s3) x.
Proof.
  unfold subst_fn; intros Hx Heq Heqx.
  unfold subst_consn.
  destruct (nth_error s0 x) eqn:Heq';
  destruct (nth_error s2 x) eqn:Heq''; auto;
  (apply nth_error_None in Heq''|| apply nth_error_None in Heq'); lia.
Qed.

Lemma shift_subst_instance :
  forall u t k,
    (subst_instance u t).[⇑^k ↑] = subst_instance u t.[⇑^k ↑].
Proof.
  intros u t k.
  rewrite /subst_instance /=.
  induction t in k |- * using term_forall_list_ind.
  all: simpl. all: auto.
  all: sigma.
  all: autorewrite with map; unfold map_branch.
  all: try solve [ f_equal ; eauto ; solve_all ; eauto ].
  - unfold Upn, shift, subst_compose, subst_consn.
    destruct (Nat.ltb_spec0 n k).
    + rewrite nth_error_idsn_Some. 1: assumption.
      reflexivity.
    + rewrite nth_error_idsn_None. 1: lia.
      reflexivity.
  - rewrite IHt1. specialize (IHt2 (S k)).
    setoid_rewrite Upn_S in IHt2.
    rewrite IHt2. reflexivity.
  - rewrite IHt1. specialize (IHt2 (S k)).
    setoid_rewrite Upn_S in IHt2.
    rewrite IHt2. reflexivity.
  - rewrite IHt1 IHt2. specialize (IHt3 (S k)).
    setoid_rewrite Upn_S in IHt3.
    rewrite IHt3. reflexivity.
  - f_equal.
    * destruct X. solve_all.
      unfold map_predicate_shift, map_predicate.
      destruct p; cbn in *; simpl; f_equal.
      + solve_all.
      + solve_all. now rewrite up_Upn -Upn_Upn.
    * apply IHt.
    * solve_all.
      unfold map_branch_shift, map_branch.
      destruct x; cbn in *; simpl; f_equal.
      + solve_all. now rewrite up_Upn -Upn_Upn.
  - f_equal.
    red in X.
    eapply All_map_eq. eapply (All_impl X).
    intros x [IH IH'].
    apply map_def_eq_spec.
    * apply IH.
    * specialize (IH' (#|m| + k)).
      sigma.
      now rewrite - !up_Upn up_up !up_Upn.
  - f_equal.
    autorewrite with len.
    red in X.
    eapply All_map_eq. eapply (All_impl X).
    intros x [IH IH'].
    apply map_def_eq_spec.
    * apply IH.
    * specialize (IH' (#|m| + k)). sigma.
      now rewrite - !up_Upn up_up !up_Upn.
Qed.

Lemma nth_error_idsn_eq_Some n k i : nth_error (idsn n) k = Some i -> i = tRel k.
Proof.
  intros hnth.
  move: (nth_error_Some_length hnth).
  len. move/nth_error_idsn_Some.
  now rewrite hnth => [= ->].
Qed.

Lemma subst_consn_ids_rel_ren n k f : (idsn n ⋅n (tRel k ⋅ ren f) ≐1 ren (ren_ids n ⋅n (subst_cons_gen k f)))%sigma.
Proof.
  intros i.
  destruct (Nat.leb_spec n i).
  - rewrite subst_consn_ge idsn_length //.
    unfold ren. f_equal. rewrite subst_consn_ge ren_ids_length; auto.
    unfold subst_cons_gen. destruct (i - n) eqn:eqin.
    * simpl. auto.
    * simpl. reflexivity.
  - assert (Hi:i < #|idsn n|) by (rewrite idsn_length; lia).
    rewrite (subst_consn_lt Hi) ren_idsn_consn_lt //.
    rewrite subst_ids_lt //.
Qed.

Lemma lift_renaming_0 k : ren (lift_renaming k 0) = ren (rshiftk k).
Proof. reflexivity. Qed.

Lemma ren_lift_renaming n k : ren (lift_renaming n k) ≐1 (⇑^k ↑^n).
Proof.
  unfold subst_compose. intros i.
  simpl. rewrite -{1}(Nat.add_0_r k). unfold ren. rewrite - (shiftn_lift_renaming n k 0).
  pose proof (ren_shiftn k (lift_renaming n 0) i).
  change ((ren (shiftn k (lift_renaming n 0)) i) = ((⇑^k (↑^n)) i)).
  rewrite -H. sigma. rewrite lift_renaming_0. reflexivity.
Qed.

Arguments Nat.sub : simpl never.

Lemma subst_consn_idsn_shift n σ : (idsn n ⋅n (σ ∘s ↑^n)) = ⇑^n σ.
Proof.
  now rewrite Upn_eq.
Qed.

Lemma Up_comp (t : term) σ : ⇑ σ ∘s (t ⋅ ids) ≐1 subst_cons t σ.
Proof.
  rewrite /Up; simpl. now sigma.
Qed.

Lemma shiftk_unfold i : (tRel i ⋅ ↑^(S i)) ≐1 ↑^i.
Proof.
  intros x; unfold subst_cons, shiftk. destruct x; lia_f_equal.
Qed.

Lemma subst_cons_compose_r t σ' σ : σ ∘s (t ⋅ σ') ≐1 ((σ 0).[t ⋅ σ'] ⋅ (↑ ∘s σ) ∘s (t ⋅ σ')).
Proof.
  intros [|i].
  - now sigma.
  - simpl.
    rewrite /subst_compose; sigma.
    unfold shift. simpl. now rewrite /subst_compose /=.
Qed.
(*
Lemma subst_consn_compose_r l σ' σ : σ ∘s (l ⋅n σ') ≐1 map (inst (σ ∘s (subst_fn l))) l ⋅n (σ ∘s σ').
Proof.
  induction l; simpl.
  - now sigma.
  - rewrite subst_consn_subst_cons.
    rewrite subst_cons_compose_r. sigma.

    rewrite (subst_cons_compose_r a

    unfold subst_compose; intros i. simpl.
    rewrite subst_compo
    rewrite IHl. now rewrite subst_consn_subst_cons.
Qed. *)

(** The central lemma to show that let expansion commutes with lifting and substitution *)
Lemma subst_reli_lift_id i n t : i <= n ->
  subst [tRel i] n (lift (S i) (S n) t) = (lift i n t).
Proof.
  intros ltin; sigma; apply inst_ext.
  rewrite Upn_eq subst_consn_idsn_shift.
  rewrite !ren_lift_renaming.
  rewrite -Nat.add_1_r Upn_Upn Upn_compose.
  now rewrite Upn_Up /= Upn_0 Up_comp shiftk_unfold.
Qed.

Lemma subst_context_lift_id Γ k n : n <= k -> subst_context [tRel n] k (lift_context (S n) (S k) Γ) = lift_context n k Γ.
Proof.
  intros nk.
  rewrite subst_context_alt !lift_context_alt.
  rewrite mapi_compose.
  apply mapi_ext; len.
  intros n' [? [?|] ?]; unfold lift_decl, subst_decl, map_decl; simpl.
  * intros. now rewrite !Nat.add_succ_r !subst_reli_lift_id //.
  * f_equal. now rewrite !Nat.add_succ_r !subst_reli_lift_id //.
Qed.

Lemma expand_lets_k_vass Γ na ty k t :
  expand_lets_k (Γ ++ [{| decl_name := na; decl_body := None; decl_type := ty |}]) k t =
  expand_lets_k Γ k t.
Proof.
  rewrite /expand_lets /expand_lets_k; len.
  rewrite extended_subst_app /=.
  rewrite subst_app_simpl. simpl. len.
  rewrite !Nat.add_1_r.
  rewrite subst_context_lift_id // lift0_context. f_equal.
  rewrite Nat.add_succ_r.
  rewrite subst_reli_lift_id //.
  move: (context_assumptions_length_bound Γ); lia.
Qed.

Lemma expand_lets_vass Γ na ty t :
  expand_lets (Γ ++ [{| decl_name := na; decl_body := None; decl_type := ty |}]) t =
  expand_lets Γ t.
Proof.
  rewrite /expand_lets; apply expand_lets_k_vass.
Qed.

Lemma expand_lets_k_vdef Γ na b ty k t :
  expand_lets_k (Γ ++ [{| decl_name := na; decl_body := Some b; decl_type := ty |}]) k t =
  expand_lets_k (subst_context [b] 0 Γ) k (subst [b] (k + #|Γ|) t).
Proof.
  rewrite /expand_lets /expand_lets_k; len.
  rewrite extended_subst_app /=.
  rewrite subst_app_simpl. simpl. len.
  rewrite !subst_empty lift0_id lift0_context.
  epose proof (distr_lift_subst_rec _ [b] (context_assumptions Γ) (k + #|Γ|) 0).
  rewrite !Nat.add_0_r in H.
  f_equal. simpl in H. rewrite Nat.add_assoc.
  rewrite <- H.
  reflexivity.
Qed.

Lemma expand_lets_vdef Γ na b ty t :
  expand_lets (Γ ++ [{| decl_name := na; decl_body := Some b; decl_type := ty |}]) t =
  expand_lets (subst_context [b] 0 Γ) (subst [b] #|Γ| t).
Proof.
  rewrite /expand_lets; apply expand_lets_k_vdef.
Qed.

Definition expand_lets_k_ctx_vass Γ k Δ na ty :
  expand_lets_k_ctx Γ k (Δ ++ [{| decl_name := na; decl_body := None; decl_type := ty |}]) =
  expand_lets_k_ctx Γ (S k) Δ ++ [{| decl_name := na; decl_body := None; decl_type :=
    expand_lets_k Γ k ty |}].
Proof.
  now  rewrite /expand_lets_k_ctx lift_context_app subst_context_app /=; simpl.
Qed.

Definition expand_lets_k_ctx_decl Γ k Δ d :
  expand_lets_k_ctx Γ k (Δ ++ [d]) = expand_lets_k_ctx Γ (S k) Δ ++ [map_decl (expand_lets_k Γ k) d].
Proof.
  rewrite /expand_lets_k_ctx lift_context_app subst_context_app /=; simpl.
  unfold app_context. simpl.
  rewrite /subst_context /fold_context_k /=.
  f_equal. rewrite compose_map_decl. f_equal.
Qed.

Lemma expand_lets_nil t : expand_lets [] t = t.
Proof. by rewrite /expand_lets /expand_lets_k /= subst_empty lift0_id. Qed.

Lemma expand_lets_it_mkProd_or_LetIn Γ Δ k t :
  expand_lets_k Γ k (it_mkProd_or_LetIn Δ t) =
  it_mkProd_or_LetIn (expand_lets_k_ctx Γ k Δ) (expand_lets_k Γ (k + #|Δ|) t).
Proof.
  revert k; induction Δ as [|[na [b|] ty] Δ] using ctx_length_rev_ind; simpl; auto; intros k.
  - now rewrite /expand_lets_k_ctx /= Nat.add_0_r.
  - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    rewrite /expand_lets_ctx expand_lets_k_ctx_decl /= it_mkProd_or_LetIn_app.
    simpl. f_equal. rewrite length_app /=.
    simpl. rewrite Nat.add_1_r Nat.add_succ_r.
    now rewrite -(H Δ ltac:(lia) (S k)).
  - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    rewrite /expand_lets_ctx expand_lets_k_ctx_decl /= it_mkProd_or_LetIn_app.
    simpl. f_equal. rewrite length_app /=.
    simpl. rewrite Nat.add_1_r Nat.add_succ_r.
    now rewrite -(H Δ ltac:(lia) (S k)).
Qed.

Lemma expand_lets_k_mkApps Γ k f args :
  expand_lets_k Γ k (mkApps f args) =
  mkApps (expand_lets_k Γ k f) (map (expand_lets_k Γ k) args).
Proof.
  now rewrite /expand_lets_k lift_mkApps subst_mkApps map_map_compose.
Qed.

Lemma expand_lets_mkApps Γ f args :
  expand_lets Γ (mkApps f args) =
  mkApps (expand_lets Γ f) (map (expand_lets Γ) args).
Proof.
  now rewrite /expand_lets expand_lets_k_mkApps.
Qed.

Lemma expand_lets_tRel k Γ :
  expand_lets Γ (tRel (k + #|Γ|)) = tRel (k + context_assumptions Γ).
Proof.
  rewrite /expand_lets /expand_lets_k.
  rewrite lift_rel_ge; try lia.
  rewrite subst_rel_gt; len; try lia.
  lia_f_equal.
Qed.

Lemma context_assumptions_context {Γ} :
  assumption_context Γ ->
  context_assumptions Γ = #|Γ|.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma assumption_context_app Γ Γ' :
  assumption_context (Γ' ,,, Γ) ->
  assumption_context Γ * assumption_context Γ'.
Proof.
  induction Γ; simpl; split; try constructor; auto.
  - depelim H. constructor; auto. now eapply IHΓ.
  - depelim H. now eapply IHΓ.
Qed.

Lemma expand_lets_k_assumption_context Γ k t :
  assumption_context Γ ->
  expand_lets_k Γ k t = t.
Proof.
  revert k.
  induction Γ using rev_ind; intros k.
  - rewrite /expand_lets /expand_lets_k /=. intros _.
    rewrite lift0_id subst_empty //.
  - intros ass. eapply assumption_context_app in ass as [assl assx].
    depelim assx.
    rewrite /expand_lets /expand_lets_k; len; simpl.
    rewrite extended_subst_app /=.
    rewrite subst_app_simpl /=; len.
    rewrite subst_context_lift_id // lift0_context.
    rewrite (context_assumptions_context assl). simpl.
    rewrite !Nat.add_1_r. replace (k + S #|l|) with (S (k + #|l|)) by lia.
    rewrite subst_reli_lift_id //; try lia.
    rewrite /expand_lets_ctx /expand_lets_k_ctx in IHΓ.
    specialize (IHΓ k assl).
    rewrite /expand_lets /expand_lets_k in IHΓ.
    now rewrite (context_assumptions_context assl) in IHΓ.
Qed.

Lemma expand_lets_assumption_context Γ t :
  assumption_context Γ ->
  expand_lets Γ t = t.
Proof.
  apply expand_lets_k_assumption_context.
Qed.

Lemma expand_lets_ctx_assumption_context Γ Δ :
  assumption_context Γ -> expand_lets_ctx Γ Δ = Δ.
Proof.
  induction Γ using rev_ind.
  - by rewrite /expand_lets_ctx /expand_lets_k_ctx /= lift0_context subst0_context.
  - intros ass. eapply assumption_context_app in ass as [assl assx].
    depelim assx.
    rewrite /expand_lets_ctx /expand_lets_k_ctx; len; simpl.
    rewrite extended_subst_app /=.
    rewrite subst_app_context /=; len.
    rewrite subst_context_lift_id // lift0_context.
    rewrite (context_assumptions_context assl). simpl.
    rewrite !Nat.add_1_r subst_context_lift_id //.
    rewrite /expand_lets_ctx /expand_lets_k_ctx in IHΓ.
    rewrite (context_assumptions_context assl) in IHΓ .
    now simpl in IHΓ.
Qed.

Lemma subst_extended_subst s Γ k : extended_subst (subst_context s k Γ) 0 =
  map (subst s (k + context_assumptions Γ)) (extended_subst Γ 0).
Proof.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto; rewrite subst_context_snoc /=;
    autorewrite with len; f_equal; auto.
  - rewrite IHΓ.
    rewrite commut_lift_subst_rec; try lia.
    rewrite distr_subst. now len.
  - elim: Nat.leb_spec => //. lia.
  - rewrite ? (lift_extended_subst _ 1); rewrite IHΓ.
    rewrite !map_map_compose. apply map_ext.
    intros x.
    erewrite (commut_lift_subst_rec); lia_f_equal.
Qed.

Lemma expand_lets_subst_comm Γ s :
  expand_lets (subst_context s 0 Γ) ∘ subst s #|Γ| ≐1 subst s (context_assumptions Γ) ∘ expand_lets Γ.
Proof.
  unfold expand_lets, expand_lets_k; simpl; intros x. len.
  rewrite !subst_extended_subst.
  rewrite distr_subst. f_equal; len.
  now rewrite commut_lift_subst_rec.
Qed.

Lemma map_expand_lets_subst_comm Γ s :
  map (expand_lets (subst_context s 0 Γ)) ∘ (map (subst s #|Γ|)) ≐1
  map (subst s (context_assumptions Γ)) ∘ (map (expand_lets Γ)).
Proof.
  intros l. rewrite !map_map_compose.
  apply map_ext. intros x; apply expand_lets_subst_comm.
Qed.

Lemma map_subst_expand_lets s Γ :
  context_assumptions Γ = #|s| ->
  subst0 (map (subst0 s) (extended_subst Γ 0)) ≐1 subst0 s ∘ expand_lets Γ.
Proof.
  intros Hs x; unfold expand_lets, expand_lets_k.
  rewrite distr_subst. f_equal.
  len.
  simpl. rewrite simpl_subst_k //.
Qed.

Lemma map_subst_expand_lets_k s Γ k x :
  context_assumptions Γ = #|s| ->
  subst (map (subst0 s) (extended_subst Γ 0)) k x = (subst s k ∘ expand_lets_k Γ k) x.
Proof.
  intros Hs; unfold expand_lets, expand_lets_k.
  epose proof (distr_subst_rec _ _ _ 0 _). rewrite -> Nat.add_0_r in H.
  rewrite -> H. clear H. f_equal.
  len.
  simpl. rewrite simpl_subst_k //.
Qed.

Lemma subst_context_map_subst_expand_lets s Γ Δ :
  context_assumptions Γ = #|s| ->
  subst_context (map (subst0 s) (extended_subst Γ 0)) 0 Δ = subst_context s 0 (expand_lets_ctx Γ Δ).
Proof.
  intros Hs. rewrite !subst_context_alt.
  unfold expand_lets_ctx, expand_lets_k_ctx.
  rewrite subst_context_alt lift_context_alt. len.
  rewrite !mapi_compose. apply mapi_ext.
  intros n x. unfold subst_decl, lift_decl.
  rewrite !compose_map_decl. apply map_decl_ext.
  intros. simpl. rewrite !Nat.add_0_r.
  generalize (Nat.pred #|Δ| - n). intros.
  rewrite map_subst_expand_lets_k //.
Qed.

Lemma subst_context_map_subst_expand_lets_k s Γ Δ k :
  context_assumptions Γ = #|s| ->
  subst_context (map (subst0 s) (extended_subst Γ 0)) k Δ = subst_context s k (expand_lets_k_ctx Γ k Δ).
Proof.
  intros Hs. rewrite !subst_context_alt.
  unfold expand_lets_ctx, expand_lets_k_ctx.
  rewrite subst_context_alt lift_context_alt. len.
  rewrite !mapi_compose. apply mapi_ext.
  intros n x. unfold subst_decl, lift_decl.
  rewrite !compose_map_decl. apply map_decl_ext.
  intros. simpl.
  rewrite map_subst_expand_lets_k //. f_equal.
  rewrite /expand_lets_k. lia_f_equal.
Qed.

Local Open Scope sigma_scope.

Lemma inst_extended_subst_shift (Γ : context) k :
  map (inst ((extended_subst Γ 0 ⋅n ids) ∘s ↑^k)) (idsn #|Γ|) =
  map (inst (extended_subst Γ k ⋅n ids)) (idsn #|Γ|).
Proof.
  intros.
  rewrite !map_idsn_spec.
  apply nat_recursion_ext => x l' Hx.
  f_equal. f_equal. simpl. rewrite subst_consn_compose.
  rewrite (@subst_consn_lt (extended_subst Γ k) x); len; try lia.
  rewrite subst_consn_lt; len; try lia.
  rewrite (lift_extended_subst _ k). now sigma.
Qed.

Lemma subst_context_decompo s s' Γ k :
  subst_context (s ++ s') k Γ =
  subst_context s' k (subst_context (map (lift0 #|s'|) s) k Γ).
Proof.
  intros.
  rewrite !subst_context_alt !mapi_compose.
  apply mapi_ext => i x.
  destruct x as [na [b|] ty] => //.
  - rewrite /subst_decl /map_decl /=; f_equal.
    + rewrite !mapi_length. f_equal.
      now rewrite subst_app_decomp.
    + rewrite mapi_length.
      now rewrite subst_app_decomp.
  - rewrite /subst_decl /map_decl /=; f_equal.
    rewrite !mapi_length. now rewrite subst_app_decomp.
Qed.

Lemma smash_context_acc Γ Δ :
  smash_context Δ Γ =
      subst_context (extended_subst Γ 0) 0 (lift_context (context_assumptions Γ) #|Γ| Δ)
   ++ smash_context [] Γ.
Proof.
  revert Δ.
  induction Γ as [|[? [] ?] ?]; intros Δ.
  - simpl; auto.
    now rewrite subst0_context app_nil_r lift0_context.
  - simpl. autorewrite with len.
    rewrite IHΓ; auto.
    rewrite subst_context_nil. f_equal.
    rewrite (subst_context_decompo [_] _).
    simpl. autorewrite with len.
    rewrite lift0_id.
    rewrite subst0_context.
    unfold subst_context, lift_context.
    rewrite !fold_context_k_compose.
    apply fold_context_k_ext. intros n x.
    rewrite Nat.add_0_r.
    autorewrite with sigma.
    apply inst_ext.
    setoid_rewrite ren_lift_renaming.
    autorewrite with sigma.
    rewrite !Upn_compose.
    apply Upn_ext.
    autorewrite with sigma.
    unfold Up.
    rewrite subst_consn_subst_cons.
    autorewrite with sigma.
    reflexivity.

  - simpl.
    rewrite IHΓ /=. auto.
    rewrite (IHΓ [_]). auto. rewrite !app_assoc. f_equal.
    rewrite app_nil_r. unfold map_decl. simpl. unfold app_context.
    simpl. rewrite lift_context_app subst_context_app /app_context. simpl.
    unfold lift_context at 2. unfold subst_context at 2, fold_context_k. simpl.
    f_equal.
    unfold subst_context, lift_context.
    rewrite !fold_context_k_compose.
    apply fold_context_k_ext. intros n x.
    rewrite Nat.add_0_r.

    autorewrite with sigma.
    apply inst_ext. rewrite !ren_lift_renaming.
    autorewrite with sigma.
    rewrite !Upn_compose.
    autorewrite with sigma.
    apply Upn_ext.
    unfold Up.

    rewrite subst_consn_subst_cons.
    autorewrite with sigma.
    apply subst_cons_proper; auto.
    rewrite !Upn_eq. autorewrite with sigma.
    rewrite subst_consn_compose.
    setoid_rewrite subst_consn_compose at 2 3.
    apply subst_consn_proper.
    { rewrite -inst_extended_subst_shift; auto. }

    autorewrite with sigma.
    rewrite -subst_compose_assoc.
    rewrite shiftk_compose.
    autorewrite with sigma.
    setoid_rewrite <- (compose_ids_l ↑) at 2.
    rewrite -subst_consn_compose.
    rewrite - !subst_compose_assoc.
    rewrite -shiftk_shift shiftk_compose.
    autorewrite with sigma.
    rewrite subst_consn_compose.
    rewrite -shiftk_compose subst_compose_assoc.
    (rewrite subst_consn_shiftn; try now autorewrite with len); [].
    autorewrite with sigma.
    rewrite -shiftk_shift.
    rewrite -shiftk_compose subst_compose_assoc.
    (rewrite subst_consn_shiftn; try now autorewrite with sigma); [].
    now autorewrite with len.
Qed.

Lemma shift_subst_consn_ge (n : nat) (l : list term) (σ : substitutionT) :
  #|l| <= n -> ↑^n ∘s (l ⋅n σ) ≐1 ↑^(n - #|l|) ∘s σ.
Proof.
  intros Hlt i.
  rewrite /subst_compose /shiftk /=.
  rewrite subst_consn_ge; try lia. lia_f_equal.
Qed.

Lemma skipn_subst n s σ :
  n <= #|s| ->
  skipn n s ⋅n σ ≐1 ↑^(n) ∘s (s ⋅n σ).
Proof.
  intros hn i.
  rewrite /subst_consn /shiftk /subst_compose /=.
  rewrite nth_error_skipn.
  destruct nth_error => //.
  rewrite List.length_skipn. lia_f_equal.
Qed.

Lemma subst_shift_comm k n s : ⇑^k s ∘s ↑^n ≐1 ↑^n ∘s ⇑^(k+n) s.
Proof.
  now rewrite Nat.add_comm Upn_Upn shiftn_Upn.
Qed.

Lemma Upn_subst_consn_ge (n i : nat) s (σ : substitutionT) :
  n + #|s| <= i -> (⇑^n (s ⋅n σ)) i = (σ ∘s ↑^n) (i - n - #|s|).
Proof.
  intros Hlt.
  rewrite /subst_compose /shiftk /= /Upn.
  rewrite subst_consn_ge; len; try lia.
  now rewrite subst_consn_compose subst_consn_ge; len; try lia.
Qed.

Lemma Upn_subst_consn_lt (n i : nat) s (σ : substitutionT) :
  i < n + #|s| -> (⇑^n (s ⋅n σ)) i = (idsn n ⋅n (subst_fn s ∘s ↑^n)) i.
Proof.
  intros Hlt.
  rewrite /subst_compose /shiftk /= /Upn.
  destruct (leb_spec_Set (S i) n).
  * rewrite subst_consn_lt; len; try lia.
    now rewrite subst_consn_lt; len; try lia.
  * rewrite subst_consn_ge; len; try lia.
    rewrite subst_consn_ge; len; try lia.
    rewrite subst_consn_compose subst_fn_subst_consn.
    rewrite !subst_consn_lt; len; try lia.
    unfold subst_fn. rewrite nth_error_map.
    case:nth_error_spec => /= // hlen. len.
    lia.
Qed.

#[global]
Hint Rewrite ren_lift_renaming subst_consn_compose : sigma.

Lemma rename_context_length :
  forall σ Γ,
    #|rename_context σ Γ| = #|Γ|.
Proof.
  intros σ Γ. unfold rename_context.
  apply fold_context_k_length.
Qed.
#[global]
Hint Rewrite rename_context_length : sigma wf.
