(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From Equations Require Import Equations.

Definition banon := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition bnamed n := {| binder_name := nNamed n; binder_relevance := Relevant |}.

Local Existing Instance config.default_checker_flags.
Import MRMonadNotation.

Definition var := nat.

Lemma eq_var (x y:var) : {x=y}+{x<>y}.
Proof.
 apply eq_nat_dec.
Defined.

Inductive form :=
| Var (x:var) | Fa | Tr | Imp (f1 f2:form) | And (f1 f2:form) | Or (f1 f2:form).

Lemma eq_form (f1 f2:form) : {f1=f2}+{f1<>f2}.
Proof.
  decide equality.
  decide equality.
Defined.

Definition not f := Imp f Fa.

Record seq := mkS { hyps : list form; concl : form }.

Fixpoint size f :=
  match f with
  | Fa | Tr => 1
  | Var _ => 1
  | Imp f1 f2 => S (size f1 + size f2)
  | And f1 f2 => S (size f1 + size f2)
  | Or f1 f2 => S (size f1 + size f2)
  end.

Definition hyps_size h :=
  List.fold_right (fun h n => n + size h) 0 h.

Definition seq_size s :=
  hyps_size (hyps s) + size (concl s).

Definition is_leaf s :=
  let cl := concl s in
  List.fold_right (fun h b => orb b (if eq_form Fa h then true else
                                       if eq_form h cl then true else false))
                  false (hyps s).

Class Propositional_Logic prop :=
  { Pfalse : prop;
    Ptrue : prop;
    Pand : prop -> prop -> prop ;
    Por : prop -> prop -> prop ;
    Pimpl : prop -> prop -> prop}.


Fixpoint semGen A `{Propositional_Logic A} f (l:var->A) :=
   match f with
  | Fa => Pfalse
  | Tr => Ptrue
  | Var x => l x
  | Imp a b => Pimpl (semGen A a l) (semGen A b l)
  | And a b => Pand (semGen A a l) (semGen A b l)
  | Or a b => Por (semGen A a l) (semGen A b l)
  end.

Local Instance Propositional_Logic_Prop : Propositional_Logic Prop :=
  {| Pfalse := False; Ptrue := True; Pand := and; Por := or; Pimpl := fun A B => A -> B |}.

Definition sem := semGen Prop.

Definition valid s :=
  forall l, (forall h, In h (hyps s) -> sem h l) -> sem (concl s) l.

Lemma is_leaf_sound s :
  is_leaf s = true -> valid s.
Proof.
unfold is_leaf.
destruct s as (h,cl); simpl.
induction h; simpl; intros.
 discriminate.
apply orb_true_elim in H; destruct H.
 apply IHh in e.
 red; simpl; intros.
 apply e; auto.

 clear IHh.
 red; simpl; intros.
 assert (sem a l).
  apply H; auto.
 clear H.
 destruct a.
  destruct (eq_form (Var x) cl); [subst cl; trivial|discriminate].

  destruct H0.
  destruct (eq_form Tr cl);[subst cl; trivial|discriminate].
  destruct (eq_form (Imp a1 a2) cl);[subst cl; trivial|discriminate].
  destruct (eq_form (And a1 a2) cl);[subst cl; trivial|discriminate].
  destruct (eq_form (Or a1 a2) cl);[subst cl; trivial|discriminate].
Qed.

Definition subgoal := list (list seq).

Definition valid_subgoal (sg:subgoal) :=
  exists2 sl, In sl sg & forall s, In s sl -> valid s.


Fixpoint pick_hyp {A} (h:list A) :=
  match h with
  | nil => nil
  | a::l =>
    (a,l)::List.map (fun p => (fst p,a::snd p)) (pick_hyp l)
  end.

Definition on_hyp h rh cl :=
  match h with
  (* Cut *)
  | Imp a b => (mkS (b::rh) cl:: mkS rh a ::nil) :: nil
  | And a b => (mkS(a::b::rh)cl::nil)::nil
  | Or a b => (mkS(a::rh)cl::mkS(b::rh)cl::nil)::nil
  | (Var _|Tr|Fa) => nil
  end.

Definition on_hyps s : subgoal :=
  List.flat_map (fun p:form*list form => let (h,rh) := p in
                                         on_hyp h rh (concl s))
                (pick_hyp (hyps s)).

Definition decomp_step s : subgoal :=
  match concl s with
  | Imp a b => (mkS (a::hyps s) b::nil)::nil
  | And a b => (mkS (hyps s) a::mkS (hyps s) b::nil)::nil
  | Or a b => (mkS(hyps s)a::nil)::(mkS(hyps s) b::nil)::on_hyps s
  | _ => on_hyps s
  end.

Inductive result := Valid | CounterModel | Abort.

Fixpoint tauto_proc n s {struct n} :=
  if is_leaf s then Valid else
    match n with
    | 0 => Abort
    | S n =>
      let fix tauto_and ls :=
          match ls with
          | nil => Valid
          | s1::ls => match tauto_proc n s1 with
                      | Valid => tauto_and ls
                      | s => s
                      end
          end in
      let fix tauto_or lls :=
          match lls with
          | ls::lls =>
            match tauto_and ls with
            | Valid => Valid
            | CounterModel => tauto_or lls
            | Abort => Abort
            end
         | nil => CounterModel
         end in
      tauto_or (decomp_step s)
end.

Definition tauto_s f := tauto_proc (size f) (mkS nil f).

Eval compute in tauto_s (Imp Fa (Var 0)).

Eval compute in tauto_s (Imp (And (Var 0) (Var 1)) (Var 0)).
Eval compute in tauto_s (Imp (And (Var 0) (Var 1)) (Var 1)).
Eval compute in tauto_s (Imp (Var 0) (Imp (Var 1) (And (Var 0) (Var 1)))).

Eval compute in tauto_s (Imp (Var 0) (Or (Var 0) (Var 1))).
Eval compute in tauto_s (Imp (Var 1) (Or (Var 0) (Var 1))).
Eval compute in tauto_s (Imp (Imp (Var 0) (Var 2)) (Imp (Imp (Var 1) (Var 2)) (Imp (Or (Var 0) (Var 1)) (Var 2)))).

Eval compute in tauto_s (Imp (Var 0) (Imp (Imp (Var 0) (Var 1)) (Var 1))).
Eval compute in tauto_s (Imp (Var 0) (Imp (Imp (Var 0) (Var 1))
                            (Imp (Imp (Var 1) (Var 2)) (Var 1)))).
Eval compute in tauto_s (Imp (Var 0) (Imp (Imp (Var 0) (Var 1))
                            (Imp (Imp (Var 1) (Var 2)) (Var 2)))).



Lemma pick_hyp_def {A} (f:A) rh h :
  In (f,rh) (pick_hyp h) <-> exists rh1 rh2, rh=rh1++rh2 /\ h = rh1++f::rh2.
Proof.
revert f rh; induction h; simpl; intros.
 split; intros.
  contradiction.
  destruct H as ([|],(?,(_,?))); discriminate.

 split.
  destruct 1.
  injection H; intros; subst f rh.
  exists nil; simpl; eauto.

  apply in_map_iff in H.
  destruct H as ((f',rh'),(?,?)); simpl in *.
  injection H; intros; subst f rh.
  destruct (IHh f' rh').
  apply H1 in H0; destruct H0 as (rh1,(rh2,(?,?))).
  clear H1 H2.
  subst.
  exists (a::rh1); simpl; eauto.

  destruct 1 as ([|],(rh2,(?,?))); simpl in *.
   injection H0; intros; subst; auto.

   right.
   injection H0; intros; subst.
   apply in_map_iff.
   exists (f,l++rh2); simpl; auto.
   split; trivial.
   apply IHh.
   eauto.
Qed.


Lemma hyps_size_app h1 h2 :
  hyps_size (h1++h2) = hyps_size h1 + hyps_size h2.
Proof.
induction h1; simpl; trivial.
rewrite IHh1.
lia.
Qed.

Lemma on_hyp_size h1 rh cl ls sg :
  In ls (on_hyp h1 rh cl) -> In sg ls -> seq_size sg < size h1 + hyps_size rh + size cl.
Proof.
unfold seq_size, on_hyp.
destruct h1; simpl.
 contradiction.
 contradiction.
 contradiction.

 destruct 1 as [? | []]; subst ls; simpl.
 destruct 1 as [?| [? | []]]; subst sg; simpl.
  lia.
  lia.

 destruct 1 as [? | []]; subst ls; simpl.
 destruct 1 as [? | []]; subst sg; simpl.
 lia.

 destruct 1 as [? | []]; subst ls; simpl.
 destruct 1 as [?| [? | []]]; subst sg; simpl.
  lia.
  lia.
Qed.

Lemma on_hyps_size s ls sg :
  In ls (on_hyps s) -> In sg ls -> seq_size sg < seq_size s.
Proof.
destruct s as (h,cl); simpl.
unfold on_hyps; simpl.
intros.
apply in_flat_map in H.
destruct H as ((h1,rh),(?,?)).
apply pick_hyp_def in H.
destruct H as (rh1&rh2&eqrh&eqh).
specialize on_hyp_size with (1:=H1) (2:=H0); intro.
unfold seq_size at 2; simpl.
subst rh h.
rewrite hyps_size_app in H |- *; simpl.
lia.
Qed.


Lemma decomp_step_size s ls sg :
  In ls (decomp_step s) -> In sg ls -> seq_size sg < seq_size s.
Proof.
destruct s as (h,cl).
unfold decomp_step; simpl.
destruct cl; simpl.
 apply on_hyps_size.

 apply on_hyps_size.
 apply on_hyps_size.

 destruct 1 as [? | []]; subst ls; simpl.
 destruct 1 as [? | []]; subst sg; simpl.
 unfold seq_size; simpl.
 lia.

 destruct 1 as [? | []]; subst ls; simpl.
 destruct 1 as [?| [? | []]]; subst sg; simpl.
  unfold seq_size; simpl.
  lia.

  unfold seq_size; simpl.
  lia.

 destruct 1 as [?| [? |? ]]; try subst ls; simpl.
  destruct 1 as [? | []]; subst sg; simpl.
  unfold seq_size; simpl.
  lia.

  destruct 1 as [? | []]; subst sg; simpl.
  unfold seq_size; simpl.
  lia.

 apply on_hyps_size; trivial.
Qed.

Lemma on_hyp_sound f rh cl :
  valid_subgoal (on_hyp f rh cl) -> valid (mkS (f::rh) cl).
Proof.
unfold on_hyp, valid_subgoal, valid; simpl; intros (sl,?,?) l ?.
(*assert (sem f l).
 auto.*)
destruct f; try (contradiction || destruct H as [ |[ ]]; subst sl).
 apply H0 with (s:=mkS (f2::rh) cl); simpl; auto.
 destruct 1; auto.
 subst h.
 apply (H1 (Imp f1 f2)); auto.
 apply H0 with (s:=mkS rh f1); simpl; auto.

 apply H0 with (s:=mkS (f1::f2::rh) cl); simpl; auto.
 destruct 1 as [|[|]]; auto.
  subst h.
  apply (H1 (And f1 f2)); simpl; auto.
  subst h.
  apply (H1 (And f1 f2)); simpl; auto.

 destruct (H1 (Or f1 f2)); simpl; auto.
  apply H0 with (s:=mkS (f1::rh) cl); simpl; auto.
  destruct 1; auto.
  subst h; auto.

  apply H0 with (s:=mkS (f2::rh) cl); simpl; auto.
  destruct 1; auto.
  subst h; auto.
Qed.

Lemma on_hyps_sound s :
  valid_subgoal (on_hyps s) ->
  valid s.
Proof.
destruct s as (h,cl); simpl.
intros (sl, ?,?).
unfold on_hyps in H.
apply in_flat_map in H.
destruct H as ((f,rh),(?,?)).
apply pick_hyp_def in H.
destruct H as (rh1,(rh2,(?,?))); simpl in *.
subst rh h.
red; simpl; intros.
apply on_hyp_sound with (f:=f) (rh:=rh1++rh2).
 exists sl; trivial.

 simpl in *.
 intros; apply H.
 apply in_or_app; simpl.
 destruct H2; auto.
 apply in_app_or in H2; destruct H2; auto.
Qed.

Lemma step_sound s :
  valid_subgoal (decomp_step s) -> valid s.
Proof.
  destruct s as (h,cl); simpl.
  unfold decomp_step; simpl.
  destruct cl; simpl; intros; try contradiction.
  apply on_hyps_sound; trivial.
  apply on_hyps_sound; trivial.
  apply on_hyps_sound; trivial.

  destruct H as (sl,[ |[ ]],?); subst sl.
  red; cbn; intros. apply (H0 _ (or_introl eq_refl)).
  simpl; intros.
  destruct H2; subst; auto.

 destruct H as (sl,[ |[ ]],?); subst sl.
 split; cbn in *.
  apply (H0 (mkS h cl1)); auto.
  apply (H0 (mkS h cl2)); auto.

 destruct H as (sl,[|[ |]],?); try subst sl.
  left.
  apply H0 with (s:=mkS h cl1); simpl; auto.

  right.
  apply H0 with (s:=mkS h cl2); simpl; auto.

  apply on_hyps_sound.
  red; eauto.
Qed.

Lemma tauto_sound n s :
  tauto_proc n s = Valid -> valid s.
Proof.
revert s; induction n; simpl; intros.
 generalize (is_leaf_sound s).
 destruct (is_leaf s); auto.
 discriminate.

 generalize (is_leaf_sound s).
 destruct (is_leaf s); auto.
 intros _.
 revert H.
 generalize (step_sound s).
 induction (decomp_step s); simpl; intros.
  discriminate.

  assert ((fix tauto_and (ls : list seq) : result :=
            match ls with
            | nil => Valid
            | s1 :: ls0 =>
                match tauto_proc n s1 with
                | Valid => tauto_and ls0
                | CounterModel => CounterModel
                | Abort => Abort
                end
            end) a = Valid \/
           (fix tauto_or (lls : list (list seq)) : result :=
              match lls with
              | nil => CounterModel
              | ls :: lls0 =>
                  match
                    (fix tauto_and (ls0 : list seq) : result :=
                       match ls0 with
                       | nil => Valid
                       | s1 :: ls1 =>
                           match tauto_proc n s1 with
                           | Valid => tauto_and ls1
                           | CounterModel => CounterModel
                           | Abort => Abort
                           end
                       end) ls
                  with
                  | Valid => Valid
                  | CounterModel => tauto_or lls0
                  | Abort => Abort
                  end
              end) s0 = Valid).
    destruct ((fix tauto_and (ls : list seq) : result :=
            match ls with
            | nil => Valid
            | s1 :: ls0 =>
                match tauto_proc n s1 with
                | Valid => tauto_and ls0
                | CounterModel => CounterModel
                | Abort => Abort
                end
          end) a); auto.
  clear H0.
  destruct H1.
   apply H; exists a; simpl; auto.
   clear H.
   induction a; simpl; intros.
    contradiction.

    generalize (IHn a).
    destruct (tauto_proc n a); intros.
     destruct H; auto.
     subst s1; auto.

     discriminate.
     discriminate.

     apply IHs0; trivial.
     intros.
     apply H.
     destruct H1.
     exists x; simpl; auto.
Qed.


MetaRocq Quote Definition MProp := Prop.

MetaRocq Quote Definition MFalse := False.

MetaRocq Quote Definition MTrue := True.

MetaRocq Quote Definition Mand := and.

MetaRocq Quote Definition Mor := or.

Definition tImpl (A B : term) :=
  tProd banon A (lift0 1 B).

Definition tAnd (A B : term) :=
  tApp Mand [ A ; B ].

Definition tOr (A B : term) :=
  tApp Mor [ A ; B ].


Inductive well_prop Σ Γ : term -> Type :=
| well_prop_Rel :
    forall n,
      Σ ;;; Γ |- tRel n : MProp ->
      well_prop Σ Γ (tRel n)

| well_prop_Impl :
    forall A B,
      well_prop Σ Γ A ->
      well_prop Σ Γ B ->
      well_prop Σ Γ (tImpl A B)

| well_prop_And :
    forall A B,
      well_prop Σ Γ A ->
      well_prop Σ Γ B ->
      well_prop Σ Γ (tAnd A B)

| well_prop_Or :
    forall A B,
      well_prop Σ Γ A ->
      well_prop Σ Γ B ->
      well_prop Σ Γ (tOr A B)

| well_prop_False : well_prop Σ Γ MFalse
| well_prop_True : well_prop Σ Γ MTrue
.



(* TODO MOVE *)
Lemma decompose_app_eq :
  forall t f args,
    decompose_app t = (f, args) ->
    t = mkApps f args \/ t = tApp f args.
Proof.
  intros t f args e.
  induction t in f, args, e |- *.
  all: simpl in e.
  all: try solve [
    inversion e ;
    left ;
    reflexivity
  ].
  inversion e. subst. right. reflexivity.
Qed.

Lemma decompose_app_wf Σ :
  forall t f args,
    WfAst.wf Σ t ->
    decompose_app t = (f, args) ->
    WfAst.wf Σ f * All (WfAst.wf Σ) args.
Proof.
  intros t f args w e.
  induction t in f, args, w, e |- *.
  all: simpl in e.
  all: inversion e ; subst.
  all: try solve [
    split ; [
      assumption
    | constructor
    ]
  ].
  inversion w. subst.
  split. all: assumption.
Qed.


Definition def_size (size : term -> nat) (x : def term) := size (dtype x) + size (dbody x).
Definition mfixpoint_size (size : term -> nat) (l : mfixpoint term) :=
  list_size (def_size size) l.
Definition decl_size (size : term -> nat) (x : context_decl) :=
  size (decl_type x) + option_default size (decl_body x) 0.

Definition context_size (size : term -> nat) (l : context) :=
  list_size (decl_size size) l.

Definition branch_size (size : term -> nat) (br : branch term) :=
  size br.(bbody).

Definition predicate_size (size : term -> nat) (p : predicate term) :=
  list_size size p.(pparams) +
  size p.(preturn).

Fixpoint tsize t : nat :=
  match t with
  | tRel i => 1
  | tEvar ev args => S (list_size tsize args)
  | tLambda na T M => S (tsize T + tsize M)
  | tApp u v => S (tsize u + list_size tsize v)
  | tProd na A B => S (tsize A + tsize B)
  | tLetIn na b t b' => S (tsize b + tsize t + tsize b')
  | tCase ind p c brs => S (predicate_size tsize p + tsize c + list_size (branch_size tsize) brs)
  | tProj p c => S (tsize c)
  | tFix mfix idx => S (mfixpoint_size tsize mfix)
  | tCoFix mfix idx => S (mfixpoint_size tsize mfix)
  | _ => 1
  end.

Lemma tsize_nonzero :
  forall t, tsize t <> 0.
Proof.
  intro t. induction t.
  all: simpl.
  all: lia.
Qed.

Lemma mkApp_tsize :
  forall u v,
    tsize (mkApp u v) <= S (S (tsize u + tsize v)).
Proof.
  intros u v.
  induction u in v |- *.
  all: simpl. all: try lia.
  rewrite list_size_app. simpl. lia.
Qed.

Lemma mkApps_tsize :
  forall t l,
    tsize (mkApps t l) <= S (tsize t + list_size tsize l).
Proof.
  intros t l.
  induction l as [| a l ih ] in t |- *.
  - simpl. lia.
  - destruct (Ast.isApp t) eqn:e.
    + destruct t. all: try discriminate.
      simpl. rewrite list_size_app. simpl. lia.
    + rewrite mkApps_tApp; eauto. discriminate.
Qed.

Lemma tsize_decompose_app :
  forall t f args,
    decompose_app t = (f, args) ->
    tsize f + list_size tsize args <= tsize t.
Proof.
  intros t f args e.
  induction t in f, args, e |- *.
  all: simpl in *.
  all: inversion e ; subst.
  all: simpl.
  all: try reflexivity.
  all: lia.
Qed.

Lemma tsize_lift :
  forall n k t,
    tsize (lift n k t) = tsize t.
Proof.
  intros n k t.
  induction t using term_forall_list_ind in n, k |- *.
  { simpl. destruct (Nat.leb_spec k n0).
    - reflexivity.
    - reflexivity.
  }
  all: simpl.
  all: try reflexivity.
  all: try easy.
  - induction H.
    + reflexivity.
    + simpl. eauto.
  - rewrite IHt. f_equal. f_equal.
    induction H.
    + reflexivity.
    + simpl. eauto.
  - solve_all.
    f_equal; auto. f_equal; eauto.
    f_equal; eauto. unfold predicate_size.
    f_equal; simpl; auto.
    induction a; simpl; auto.
    induction X0; simpl; auto.
    f_equal; auto. f_equal; auto.
    unfold branch_size; simpl; auto.
  - generalize (#|m| + k). intro p.
    induction X.
    + reflexivity.
    + simpl. unfold map_def. unfold def_size.
      simpl.
      intuition eauto.
  - generalize (#|m| + k). intro p.
    induction X.
    + reflexivity.
    + simpl. unfold map_def. unfold def_size.
      simpl.
      intuition eauto.
Qed.

Lemma list_size_length :
  forall l,
    list_size tsize l >= #|l|.
Proof.
  intros l. induction l.
  - auto.
  - simpl. pose proof (tsize_nonzero a). lia.
Qed.

Lemma nth_error_list_size :
  forall n l t,
    nth_error l n = Some t ->
    tsize t <= list_size tsize l + 1 - #|l|.
Proof.
  intros n l t e.
  induction l in n, t, e |- *.
  - destruct n. all: inversion e.
  - destruct n.
    + simpl in e. apply some_inj in e. subst.
      simpl. pose proof (list_size_length l). lia.
    + simpl in e. simpl.
      eapply IHl in e. lia.
Qed.

Lemma tsize_downlift :
  forall Σ t k,
    WfAst.wf Σ t ->
    tsize (subst [tRel 0] k t) = tsize t.
Proof.
  intros Σ t k h.
  induction h using WfAst.term_wf_forall_list_ind in k |- *.
  { simpl. destruct (Nat.leb_spec k n).
    - destruct (n - k) as [|m].
      + simpl. reflexivity.
      + simpl. destruct m. all: reflexivity.
    - reflexivity.
  }
  all: simpl; auto.
  all: try solve [ eauto ].
  - f_equal. induction X.
    + reflexivity.
    + simpl. specialize (p k). congruence.
  - rewrite mkApps_tApp; eauto.
    + simpl. f_equal. rewrite IHh by assumption. f_equal.
      clear - X0. induction X0.
      * reflexivity.
      * cbn. specialize (p k); congruence.
    + clear - H. destruct t.
      all: simpl in *.
      all: try solve [ eauto ].
      destruct (Nat.leb_spec k n).
      * destruct (n - k) as [|m].
        -- simpl. reflexivity.
        -- simpl. destruct m. all: eauto.
      * simpl. reflexivity.
    + clear - H0. destruct l. contradiction.
      discriminate.
  - f_equal.
    f_equal; solve_all.
    unfold predicate_size. simpl. f_equal; auto.
    f_equal; auto. clear H0 H1. induction a; simpl; auto.
    unfold branch_size.
    clear -X1.
    induction X1; simpl; auto.
    destruct r. f_equal; auto.
  - f_equal.
    generalize (#|m| + k). intro p.
    clear - X. induction X.
    + reflexivity.
    + destruct p0. subst.
      unfold mfixpoint_size.
      unfold map_def. unfold def_size.
      simpl. f_equal. intuition eauto.
  - f_equal.
    generalize (#|m| + k). intro p.
    clear - X. induction X.
    + reflexivity.
    + destruct p0. subst.
      unfold mfixpoint_size.
      unfold map_def. unfold def_size.
      simpl. f_equal. intuition eauto.
Qed.

Local Ltac inst :=
  lazymatch goal with
  | h : forall k, _ <= tsize ?x |- context [ (subst _ ?k ?x) ] =>
    specialize (h k)
  end.

Lemma tsize_downlift_le :
  forall t k,
    tsize (subst [tRel 0] k t) <= tsize t.
Proof.
  intros t k.
  induction t using term_forall_list_ind in k |- *.
  { simpl. destruct (Nat.leb_spec k n).
    - destruct (n - k) as [|m].
      + simpl. reflexivity.
      + simpl. destruct m. all: reflexivity.
    - reflexivity.
  }
  all: simpl.
  all: try solve [ eauto ].
  all: try solve [ repeat inst ; lia ].
  - eapply le_n_S. induction H.
    + reflexivity.
    + simpl. repeat inst. lia.
  - inst.
    pose proof (mkApps_tsize (subst [tRel 0] k t) (map (subst [tRel 0] k) l)) as h.
    assert (list_size tsize (map (subst [tRel 0] k) l) <= list_size tsize l).
    { clear - H. induction H.
      - reflexivity.
      - simpl. inst. lia.
    }
    lia.
  - repeat inst.

    assert (
      list_size (branch_size tsize) (map_branches_k (subst [tRel 0]) k l)
      <= list_size (branch_size tsize) l
    ).
    { unfold branch_size.
      clear - X0. induction X0.
    - reflexivity.
    - simpl. inst. lia.
     }
    assert (predicate_size tsize (map_predicate id (subst [tRel 0] k) (subst [tRel 0] (#|pcontext t| + k)) t) <=
      predicate_size tsize t).
    { apply Nat.add_le_mono; simpl; auto. 2:apply X. destruct X.
      induction a; simpl; auto. apply le_n_S, Nat.add_le_mono; simpl; auto. }
  lia.
  - eapply le_n_S.
    generalize (#|m| + k). intro p.
    clear - X. induction X.
    + reflexivity.
    + unfold mfixpoint_size.
      unfold map_def. unfold def_size.
      simpl.
      intuition eauto.
      unfold mfixpoint_size in IHX.
      unfold map_def in IHX.
      unfold def_size in IHX.
      repeat inst. lia.
  - eapply le_n_S.
    generalize (#|m| + k). intro p.
    clear - X. induction X.
    + reflexivity.
    + unfold mfixpoint_size.
      unfold map_def. unfold def_size.
      simpl.
      intuition eauto.
      unfold mfixpoint_size in IHX.
      unfold map_def in IHX.
      unfold def_size in IHX.
      repeat inst. lia.
Qed.

Definition tmLocateInd (q : qualid) : TemplateMonad kername :=
  l <- tmLocate q ;;
  match l with
  | [] => tmFail ("Inductive [" ^ q ^ "] not found")
  | (IndRef ind) :: _ => tmReturn ind.(inductive_mind)
  | _ :: _ => tmFail ("[" ^ q ^ "] not an inductive")
  end.


MetaRocq Run (tmLocateInd "Logic.and" >>= tmDefinition "q_and").
MetaRocq Run (tmLocateInd "Logic.or" >>= tmDefinition "q_or").
MetaRocq Run (tmLocateInd "Logic.True" >>= tmDefinition "q_True").
MetaRocq Run (tmLocateInd "Logic.False" >>= tmDefinition "q_False").

Equations reify (Σ : global_env_ext) (Γ : context) (P : term) : option form
  by wf (tsize P) lt :=
  reify Σ Γ P with inspect (decompose_app P) := {
  | @exist (hd, args) e1 with hd := {
    | tRel n with nth_error Γ n := {
      | Some decl => Some (Var n) ;
      | None => None
      } ;
    | tInd ind []
      with eqb ind.(inductive_mind) q_and := {
      | true with args := {
        | [ A ; B ] =>
          af <- reify Σ Γ A ;;
          bf <- reify Σ Γ B ;;
          ret (And af bf) ;
        | _ => None
        } ;
      | false
        with eqb ind.(inductive_mind) q_or := {
        | true with args := {
          | [ A ; B ] =>
            af <- reify Σ Γ A ;;
            bf <- reify Σ Γ B ;;
            ret (Or af bf) ;
          | _ => None
          } ;
        | false
          with eqb ind.(inductive_mind) q_False := {
          | true with args := {
            | [] => ret Fa ;
            | _ => None
            } ;
      | false
          with eqb ind.(inductive_mind) q_True := {
          | true with args := {
            | [] => ret Tr ;
            | _ => None
            } ;
              | false => None
       }
        }
      }} ;
    | tProd na A B =>
      af <- reify Σ Γ A ;;
      bf <- reify Σ Γ (subst [tRel 0] 0 B) ;;
      ret (Imp af bf) ;
    | _ => None
    }
  }.
Next Obligation.
  apply tsize_decompose_app in e1 as h1.
  simpl in h1. lia.
Qed.
Next Obligation.
  apply tsize_decompose_app in e1 as h1.
  simpl in h1. pose proof (tsize_downlift_le B 0).
  lia.
Qed.
Next Obligation.
  apply tsize_decompose_app in e1 as h1.
  simpl in h1. lia.
Qed.
Next Obligation.
  apply tsize_decompose_app in e1 as h1.
  simpl in h1. lia.
Qed.
Next Obligation.
  apply tsize_decompose_app in e1 as h1.
  simpl in h1. lia.
Qed.
Next Obligation.
  apply tsize_decompose_app in e1 as h1.
  simpl in h1. lia.
Qed.

Local Instance Propositional_Logic_MetaRocq : Propositional_Logic term :=
  {| Pfalse := MFalse; Ptrue := MTrue; Pand := fun P Q => mkApps Mand [P;Q];
     Por := fun P Q => mkApps Mor [P;Q]; Pimpl := fun P Q => tImpl P Q |}.

Definition Msem := semGen term.

Definition can_val (v : var) : term := tRel v.

Definition can_val_Prop (Γ : list Prop) (v : var) : Prop :=
  match nth_error Γ v with
  | Some P => P
  | None => False
  end.

Lemma inversion_Rel :
  forall {Σ Γ n T},
    Σ ;;; Γ |- tRel n : T ->
    ∑ decl,
      (wf_local Σ Γ) *
      (nth_error Γ n = Some decl) *
      (Σ ;;; Γ |- lift0 (S n) (decl_type decl) <= T).
Admitted.

Lemma well_prop_wf :
  forall Σ Γ P,
    well_prop Σ Γ P ->
    WfAst.wf Σ P.
Proof.
  intros Σ Γ P h.
  induction h.
  all: try solve [ constructor ; auto using WfAst.wf_lift ].
  - constructor. all: try easy.
    constructor.
  - constructor. all: try easy.
    constructor.
Qed.

Local Set Keyed Unification.

Definition reify_correct :
  forall Σ Γ P,
    well_prop Σ Γ P ->
    exists φ, reify Σ Γ P = Some φ /\ Msem φ can_val = P.
Proof.
  intros Σ Γ P h.
  induction h.
  - exists (Var n). split.
    + simp reify. simpl. apply inversion_Rel in t as [? [[? e] ?]].
      rewrite e. reflexivity.
    + reflexivity.
  - destruct IHh1 as [fA [r1 s1]].
    destruct IHh2 as [fB [r2 s2]].
    exists (Imp fA fB). split.
    + simp reify.
      apply well_prop_wf in h2 as w2.
      rewrite (simpl_subst_k Σ) by auto.
      simp reify in r1. rewrite r1.
      simp reify in r2. rewrite r2.
      reflexivity.
    + cbn. rewrite s1, s2. reflexivity.
  - destruct IHh1 as [fA [r1 s1]].
    destruct IHh2 as [fB [r2 s2]].
    exists (And fA fB). split.
    + simp reify.
      simp reify in r1. rewrite r1.
      simp reify in r2. rewrite r2.
      simpl. reflexivity.
    + cbn. rewrite s1, s2. reflexivity.
  - destruct IHh1 as [fA [r1 s1]].
    destruct IHh2 as [fB [r2 s2]].
    exists (Or fA fB). split.
    + simp reify.
      simp reify in r1. rewrite r1.
      simp reify in r2. rewrite r2.
      simpl. reflexivity.
    + cbn. rewrite s1, s2. reflexivity.
  - exists Fa. split.
    + rewrite reify_unfold_eq. reflexivity.
    + reflexivity.
  - exists Tr. split.
    + rewrite reify_unfold_eq. reflexivity.
    + reflexivity.
Qed.


Section Plugin.

  Definition cdecl_Type (P:term) :=
    {| decl_name := banon; decl_body := None; decl_type := P |}.

  Definition trivial_hyp (h:list form) v : forall h : form, In h [] -> sem h v.
    intro. destruct 1.
  Qed.

  Transparent reify.

  Inductive NotSolvable (s: string) : Prop := notSolvable: NotSolvable s.

  Definition inhabit_formula gamma Mphi Gamma :
    match reify (empty_ext empty_global_env) gamma Mphi with
      Some phi =>
      match tauto_proc (size phi) {| hyps := []; concl := phi |} with
        Valid => sem (concl {| hyps := []; concl := phi |}) (can_val_Prop Gamma)
      | _ => NotSolvable "not a valid formula" end
    | None => NotSolvable "not a formaula" end.
    destruct (reify (empty_ext _) gamma Mphi); try exact (notSolvable _).
    destruct (tauto_proc (size f) {| hyps := []; concl := f |}) eqn : e; try exact (notSolvable _).
    exact (tauto_sound (size f) (mkS [] f) e (can_val_Prop Gamma) (trivial_hyp [] _)).
  Defined.

  Fixpoint extract_form (P:term) (n : nat) : term * nat :=
    match P with
    | tProd _ (tSort _) P' =>
      extract_form P' (S n)
    | _ => (P,n)
    end.

  Fixpoint Prop_ctx (n:nat) :=
    match n with O => []
            | S n => cdecl_Type MProp :: Prop_ctx n
    end.

  Ltac extract_form_tac k l :=
    match goal with | |- forall X:Prop, _ =>
                      let H := fresh "H" in
                      intros H;
                     extract_form_tac k ltac:(constr:(H::l))
    | |- _ => k l end.

  Ltac Mtauto l T H :=
    let k x :=
        pose proof (let Mphi := extract_form x 0 in inhabit_formula (Prop_ctx (snd Mphi)) (fst Mphi) l) as H; compute in H
      in
        quote_term T k.

  Ltac tauto :=
    let L := fresh "L" in
    let P := fresh "P" in
    match goal with | |- ?T => extract_form_tac
                                 ltac:(fun l => pose (L:=l); pose (P:=T))
                                        (@nil Prop) end;
    let H := fresh "H" in
    Mtauto L ltac:(eval compute in P) H;
    first [match goal with | H : NotSolvable ?s |- _ => fail 2 s end
         | exact H].

  Lemma test : forall (A B C:Prop), (A->C)->(B->C)->A\/B->C.
    tauto.
  Qed.

  Lemma test2 : forall (A B C:Prop), (A->C)->(B->C)->A\/B->B.
    Fail tauto.
  Abort.

End Plugin.
