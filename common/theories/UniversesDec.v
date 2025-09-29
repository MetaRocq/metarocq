From Stdlib Require Import PArith NArith ZArith Lia.
From MetaRocq.Utils Require Import MRList MROption MRUtils.
From MetaRocq.Common Require Import uGraph.
From MetaRocq.Common Require Import Universes.
(* Import wGraph. *)

Definition levels_of_cs (cstr : UnivConstraintSet.t) : LevelSet.t
  := UnivConstraintSet.fold (fun '(l1, _, l2) acc => LevelSet.add l1 (LevelSet.add l2 acc)) cstr (LevelSet.singleton Level.lzero).
Lemma levels_of_cs_spec cstr (lvls := levels_of_cs cstr)
  : uGraph.global_uctx_invariants (lvls, cstr).
Proof.
  subst lvls; cbv [levels_of_cs].
  cbv [uGraph.global_uctx_invariants uGraph.uctx_invariants UnivConstraintSet.For_all declared_univ_cstr_levels]; cbn [fst snd ContextSet.levels ContextSet.constraints].
  repeat first [ apply conj
               | progress intros
               | progress destruct ?
               | match goal with
                 | [ |- ?x \/ ?y ]
                   => first [ lazymatch x with context[LevelSet.In ?l (LevelSet.singleton ?l)] => idtac end;
                              left
                            | lazymatch y with context[LevelSet.In ?l (LevelSet.singleton ?l)] => idtac end;
                              right ]
                 | [ H : UnivConstraintSet.In ?l ?c |- ?x \/ ?y ]
                   => first [ lazymatch x with context[LevelSet.In _ (UnivConstraintSet.fold _ c _)] => idtac end;
                              left
                            | lazymatch y with context[LevelSet.In _ (UnivConstraintSet.fold _ c _)] => idtac end;
                              right ]
                 end
               | rewrite !LevelSet.union_spec
               | progress rewrite <- ?UnivConstraintSet.elements_spec1, ?InA_In_eq in *
               | rewrite ConstraintSetProp.fold_spec_right ].
  all: lazymatch goal with
       | [ |- LevelSet.In Level.lzero (List.fold_right ?f ?init ?ls) ]
         => first [ LevelSetDecide.fsetdec
                  | cut (LevelSet.In Level.lzero init);
                    [ generalize init; induction ls; intros; cbn in *
                    | LevelSetDecide.fsetdec ] ]
       | [ H : List.In ?v ?ls |- LevelSet.In ?v' (List.fold_right ?f ?init (List.rev ?ls)) ]
         => rewrite List.in_rev in H;
            let ls' := fresh "ls" in
            set (ls' := List.rev ls);
            change (List.In v ls') in H;
            change (LevelSet.In v' (List.fold_right f init ls'));
            generalize init; induction ls'; cbn in *
       end.
  all: repeat first [ exfalso; assumption
                    | progress destruct_head'_or
                    | progress subst
                    | progress intros
                    | progress destruct ?
                    | rewrite !LevelSetFact.add_iff
                    | solve [ auto ] ].
Qed.

Definition consistent_dec ctrs : {@consistent ctrs} + {~@consistent ctrs}.
Proof.
  pose proof (@uGraph.is_consistent_spec config.default_checker_flags (levels_of_cs ctrs, ctrs) (levels_of_cs_spec ctrs)) as H.
  destruct uGraph.is_consistent; [ left; apply H | right; intro H'; apply H in H' ]; auto.
Defined.

Definition levels_of_cs2 (cs1 cs2 : UnivConstraintSet.t) : LevelSet.t
  := LevelSet.union (levels_of_cs cs1) (levels_of_cs cs2).
Lemma levels_of_cs2_spec cs1 cs2 (lvls := levels_of_cs2 cs1 cs2)
  : uGraph.global_uctx_invariants (lvls, cs1)
    /\ uGraph.global_uctx_invariants (lvls, cs2).
Proof.
  split; apply global_uctx_invariants_union_or; constructor; apply levels_of_cs_spec.
Qed.

Definition levels_of_cscs (cs : ContextSet.t) (cstr : UnivConstraintSet.t) : LevelSet.t
  := LevelSet.union (ContextSet.levels cs) (levels_of_cs2 cstr (ContextSet.constraints cs)).
Lemma levels_of_cscs_spec cs cstr (lvls := levels_of_cscs cs cstr)
  : uGraph.global_uctx_invariants (lvls, ContextSet.constraints cs)
    /\ uGraph.global_uctx_invariants (lvls, cstr).
Proof.
  generalize (levels_of_cs2_spec cstr (ContextSet.constraints cs)).
  split; apply global_uctx_invariants_union_or; constructor; apply levels_of_cs2_spec.
Qed.

Definition levels_of_universe (u : Universe.t) : VSet.t
  := LevelExprSet.fold
       (fun gc acc => match LevelExpr.get_noprop gc with
                      | Some l => VSet.add l acc
                      | None => acc
                      end)
       u
       VSet.empty.
Lemma levels_of_universe_spec u cstr (lvls := levels_of_universe u)
  : gc_levels_declared (lvls, cstr) u.
Proof.
  subst lvls; cbv [levels_of_universe gc_levels_declared gc_expr_declared on_Some_or_None LevelExpr.get_noprop]; cbn [fst snd].
  cbv [LevelExprSet.For_all]; cbn [fst snd].
  repeat first [ apply conj
               | progress intros
               | progress destruct ?
               | exact I
               | progress rewrite <- ?LevelExprSet.elements_spec1, ?InA_In_eq in *
               | rewrite LevelExprSetProp.fold_spec_right ].
  all: lazymatch goal with
       | [ H : List.In ?v ?ls |- VSet.In ?v' (List.fold_right ?f ?init (List.rev ?ls)) ]
         => rewrite List.in_rev in H;
            let ls' := fresh "ls" in
            set (ls' := List.rev ls);
            change (List.In v ls') in H;
            change (VSet.In v' (List.fold_right f init ls'));
            generalize init; induction ls'; cbn in *
       end.
  all: repeat first [ exfalso; assumption
                    | progress destruct_head'_or
                    | progress subst
                    | progress intros
                    | progress destruct ?
                    | rewrite !VSetFact.add_iff
                    | solve [ auto ] ].
Qed.

(** Gives an equivalent pair of [((lvls, cs), cstr)] such that
- [global_uctx_invariants (lvls, cs)]
- all levels used in cs are in lvls
- and constraints mentioning levels not in the original [lvls] are refreshed
 *)
Definition uniquify_level_level (shared_levels : LevelSet.t) (shared_prefix : Byte.byte) (prefix : Byte.byte) (x : string) : string
  := (String.String
        (if LevelSet.mem (Level.level x) shared_levels
         then shared_prefix
         else prefix)
        x).
Definition ununiquify_level_level (x : string) : string
  := match x with
     | String.EmptyString => String.EmptyString
     | String.String _ x => x
     end.
Definition uniquify_level_var (shared_levels : LevelSet.t) (total_sets : nat) (offset : nat) (x : nat) : nat
  := x * S total_sets + (if LevelSet.mem (Level.lvar x) shared_levels
                         then O
                         else S offset).
Definition ununiquify_level_var (total_sets : nat) (x : nat) : nat
  := Z.to_nat (Z.of_nat x / Z.of_nat (S total_sets)).
Definition uniquify_level (shared_levels : LevelSet.t) (shared_prefix : Byte.byte) (total_sets : nat) (prefix : Byte.byte) (offset : nat) (lvl : Level.t) : Level.t
  := match lvl with
     | Level.lzero => Level.lzero
     | Level.level x => Level.level (uniquify_level_level shared_levels shared_prefix prefix x)
     | Level.lvar x => Level.lvar (uniquify_level_var shared_levels total_sets offset x)
     end.
Definition ununiquify_level (total_sets : nat) (lvl : Level.t) : Level.t
  := match lvl with
     | Level.lzero => Level.lzero
     | Level.level x => Level.level (ununiquify_level_level x)
     | Level.lvar x => Level.lvar (ununiquify_level_var total_sets x)
     end.
Definition uniquify_constraint (shared_levels : LevelSet.t) (shared_prefix : Byte.byte) (total_sets : nat) (prefix : Byte.byte) (offset : nat) (c : UnivConstraintSet.elt) : UnivConstraintSet.elt
  := let '((l1, c), l2) := c in
     let u := uniquify_level shared_levels shared_prefix total_sets prefix offset in
     ((u l1, c), u l2).
Definition ununiquify_constraint (total_sets : nat) (c : UnivConstraintSet.elt) : UnivConstraintSet.elt
  := let '((l1, c), l2) := c in
     let u := ununiquify_level total_sets in
     ((u l1, c), u l2).
Definition uniquify_valuation (shared_levels : LevelSet.t) (shared_prefix : Byte.byte) (total_sets : nat) (prefix : Byte.byte) (offset : nat) (v : valuation) : valuation
  := {| valuation_mono s
       := v.(valuation_mono) (uniquify_level_level shared_levels shared_prefix prefix s)
     ; valuation_poly n
       := v.(valuation_poly) (uniquify_level_var shared_levels total_sets offset n)
     |}.
Definition ununiquify_valuation (total_sets : nat) (v : valuation) : valuation
  := {| valuation_mono s
       := v.(valuation_mono) (ununiquify_level_level s)
     ; valuation_poly n
       := v.(valuation_poly) (ununiquify_level_var total_sets n)
     |}.
Definition uniquify_level_for lvls (side:bool) lvl
  := uniquify_level lvls "b"%byte 2 (if side then "l" else "r")%byte (if side then 0 else 1) lvl.
Definition uniquify_constraint_for lvls (side:bool) c
  := uniquify_constraint lvls "b"%byte 2 (if side then "l" else "r")%byte (if side then 0 else 1) c.
Definition uniquify_valuation_for lvls (side:bool) v
  := uniquify_valuation lvls "b"%byte 2 (if side then "l" else "r")%byte (if side then 0 else 1) v.
Definition declare_and_uniquify_levels : ContextSet.t * UnivConstraintSet.t -> ContextSet.t * UnivConstraintSet.t
  := fun '(cs, cstr)
     => let '(lvls, cs) := (ContextSet.levels cs, ContextSet.constraints cs) in
        let '(cs_all_lvls, cstr_all_lvls) := (levels_of_cs cs, levels_of_cs cstr) in
        ((LevelSet.fold
            (fun l => LevelSet.add (uniquify_level_for lvls true l))
            cs_all_lvls
            (LevelSet.fold
               (fun l => LevelSet.add (uniquify_level_for lvls true l))
               lvls
               (LevelSet.singleton Level.lzero)),
           UnivConstraintSet.fold
             (fun c => UnivConstraintSet.add (uniquify_constraint_for lvls true c))
             cs
             UnivConstraintSet.empty),
           UnivConstraintSet.fold
             (fun c => UnivConstraintSet.add (uniquify_constraint_for lvls false c))
             cstr
             UnivConstraintSet.empty).

Definition declare_and_uniquify_and_combine_levels : ContextSet.t * UnivConstraintSet.t -> ContextSet.t * UnivConstraintSet.t
  := fun '(cs, cstr)
     => let cscstr := declare_and_uniquify_levels (cs, cstr) in
        let '(cs, cstr) := (cscstr.1, cscstr.2) in
        (cs, UnivConstraintSet.union cstr (ContextSet.constraints cs)).

Definition combine_valuations (shared_prefix prefixl prefixr : Byte.byte) (total_sets : nat := 2) (vd vl vr : valuation) : valuation
  := let __ := reflectEq_Z in
     {| valuation_mono s
       := match s with
          | ""%bs => vd.(valuation_mono) s
          | String.String p _
            => if p == shared_prefix
               then vd.(valuation_mono) s
               else if p == prefixl
                    then vl.(valuation_mono) s
                    else if p == prefixr
                         then vr.(valuation_mono) s
                         else vd.(valuation_mono) s
          end
     ; valuation_poly n
       := let r := (Z.of_nat n mod 3)%Z in
          if r == 0%Z
          then vd.(valuation_poly) n
          else if r == 1%Z
               then vl.(valuation_poly) n
               else if r == 2%Z
                    then vr.(valuation_poly) n
                    else vd.(valuation_poly) n
     |}.

Lemma ConstraintSet_In_fold_add c cs1 cs2 f
  : UnivConstraintSet.In c (UnivConstraintSet.fold (fun c => UnivConstraintSet.add (f c)) cs1 cs2)
    <-> (UnivConstraintSet.Exists (fun c' => c = f c') cs1 \/ UnivConstraintSet.In c cs2).
Proof.
  cbv [UnivConstraintSet.Exists]; rewrite ConstraintSetProp.fold_spec_right.
  setoid_rewrite (ConstraintSetFact.elements_iff cs1).
  setoid_rewrite InA_In_eq.
  setoid_rewrite (@List.in_rev _ (UnivConstraintSet.elements cs1)).
  induction (List.rev (UnivConstraintSet.elements cs1)) as [|x xs IH]; cbn [List.In List.fold_right];
    [ now firstorder idtac | ].
  rewrite UnivConstraintSet.add_spec.
  repeat first [ progress destruct_head'_ex
               | progress destruct_head'_and
               | progress destruct_head'_or
               | progress subst
               | progress intuition eauto ].
Qed.

Lemma LevelSet_In_fold_add c cs1 cs2 f
  : LevelSet.In c (LevelSet.fold (fun c => LevelSet.add (f c)) cs1 cs2)
    <-> (LevelSet.Exists (fun c' => c = f c') cs1 \/ LevelSet.In c cs2).
Proof.
  cbv [LevelSet.Exists]; rewrite LevelSetProp.fold_spec_right.
  setoid_rewrite (LevelSetFact.elements_iff cs1).
  setoid_rewrite InA_In_eq.
  setoid_rewrite (@List.in_rev _ (LevelSet.elements cs1)).
  induction (List.rev (LevelSet.elements cs1)) as [|x xs IH]; cbn [List.In List.fold_right];
    [ now firstorder idtac | ].
  rewrite LevelSet.add_spec.
  repeat first [ progress destruct_head'_ex
               | progress destruct_head'_and
               | progress destruct_head'_or
               | progress subst
               | progress intuition eauto ].
Qed.

Lemma ununiquify_level_var__uniquify_level_var lvls n offset v (Hn : offset < n)
  : ununiquify_level_var n (uniquify_level_var lvls n offset v) = v.
Proof.
  cbv [uniquify_level_var ununiquify_level_var].
  destruct ?; f_equal.
  all: Z.to_euclidean_division_equations; nia.
Qed.

Lemma ununiquify_level_level__uniquify_level_level lvls sp p v
  : ununiquify_level_level (uniquify_level_level lvls sp p v) = v.
Proof. reflexivity. Qed.

Lemma ununiquify_level__uniquify_level lvls n offset sp p v (Hn : offset < n)
  : ununiquify_level n (uniquify_level lvls sp n p offset v) = v.
Proof.
  destruct v; try reflexivity.
  cbv [ununiquify_level uniquify_level].
  f_equal; now apply ununiquify_level_var__uniquify_level_var.
Qed.

Lemma ConstraintSet_In__declare_and_uniquify_and_combine_levels_1__0 cs cstr c
  : UnivConstraintSet.In c (ContextSet.constraints cs)
    -> UnivConstraintSet.In (uniquify_constraint_for (ContextSet.levels cs) true c) (ContextSet.constraints (declare_and_uniquify_and_combine_levels (cs, cstr)).1).
Proof.
  cbv [declare_and_uniquify_levels declare_and_uniquify_and_combine_levels uniquify_constraint_for uniquify_constraint].
  repeat first [ progress subst
               | progress cbn [ContextSet.constraints fst snd]
               | progress cbv [UnivConstraintSet.Exists]
               | destruct ?
               | rewrite ConstraintSet_In_fold_add
               | solve [ eauto ] ].
Qed.

Lemma ConstraintSet_In__declare_and_uniquify_and_combine_levels_1__1 cs cstr c
  : UnivConstraintSet.In c (ContextSet.constraints (declare_and_uniquify_and_combine_levels (cs, cstr)).1)
    -> UnivConstraintSet.In (ununiquify_constraint 2 c) (ContextSet.constraints cs).
Proof.
  cbv [declare_and_uniquify_levels declare_and_uniquify_and_combine_levels ununiquify_constraint uniquify_constraint_for uniquify_constraint].
  repeat first [ progress subst
               | progress cbn [ContextSet.constraints fst snd]
               | progress cbv [UnivConstraintSet.Exists]
               | destruct ?
               | rewrite ConstraintSet_In_fold_add
               | rewrite ConstraintSetFact.empty_iff
               | progress intros
               | progress destruct_head'_and
               | progress destruct_head'_or
               | progress destruct_head'_ex
               | progress destruct_head'_False
               | rewrite ununiquify_level__uniquify_level by lia
               | match goal with
                 | [ H : (_, _) = (_, _) |- _ ] => inv H
                 end
               | solve [ eauto ] ].
Qed.

Lemma ConstraintSet_In__declare_and_uniquify_and_combine_levels_2__0 cs cstr c
  : UnivConstraintSet.In c cstr
    -> UnivConstraintSet.In (uniquify_constraint_for (ContextSet.levels cs) false c) (declare_and_uniquify_and_combine_levels (cs, cstr)).2.
Proof.
  cbv [declare_and_uniquify_levels declare_and_uniquify_and_combine_levels uniquify_constraint_for uniquify_constraint].
  repeat first [ progress subst
               | progress cbn [ContextSet.constraints fst snd]
               | progress cbv [UnivConstraintSet.Exists]
               | destruct ?
               | rewrite ConstraintSet_In_fold_add
               | rewrite UnivConstraintSet.union_spec
               | solve [ eauto ] ].
Qed.

Lemma ConstraintSet_In__declare_and_uniquify_levels_2__1 cs cstr c
  : UnivConstraintSet.In c (declare_and_uniquify_levels (cs, cstr)).2
    -> UnivConstraintSet.In (ununiquify_constraint 2 c) cstr.
Proof.
  cbv [declare_and_uniquify_levels ununiquify_constraint uniquify_constraint_for uniquify_constraint].
  repeat first [ progress subst
               | progress cbn [ContextSet.constraints fst snd]
               | progress cbv [UnivConstraintSet.Exists]
               | destruct ?
               | rewrite ConstraintSet_In_fold_add
               | rewrite ConstraintSetFact.empty_iff
               | progress intros
               | progress destruct_head'_and
               | progress destruct_head'_or
               | progress destruct_head'_ex
               | progress destruct_head'_False
               | rewrite ununiquify_level__uniquify_level by lia
               | match goal with
                 | [ H : (_, _) = (_, _) |- _ ] => inv H
                 end
               | solve [ eauto ] ].
Qed.

Lemma LevelSet_In_declare_and_uniquify_and_combine_levels_1_1 cs cstr side x
  : LevelSet.In x (ContextSet.levels cs)
    -> LevelSet.In (uniquify_level_for (ContextSet.levels cs) side x)
         (ContextSet.levels (declare_and_uniquify_and_combine_levels (cs, cstr)).1).
Proof.
  cbv [declare_and_uniquify_and_combine_levels declare_and_uniquify_levels ContextSet.levels]; cbn [fst snd].
  rewrite !LevelSet_In_fold_add.
  intro Hx.
  repeat lazymatch goal with
         | [ |- ?x \/ ?y ]
           => first [ lazymatch x with
                      | context[LevelSet.Exists _ cs.1] => left
                      end
                    | lazymatch y with
                      | context[LevelSet.Exists _ cs.1] => right
                      end ]
         end.
  cbv [LevelSet.Exists uniquify_level_var uniquify_level_level uniquify_level_for uniquify_level].
  exists x; split; trivial.
  destruct x; try reflexivity.
  all: now rewrite LevelSetFact.mem_1 by assumption.
Qed.

Lemma satisfies_declare_and_uniquify_and_combine_levels_1_0 {cs cstr v}
  : satisfies v (ContextSet.constraints (declare_and_uniquify_and_combine_levels (cs, cstr)).1)
    -> satisfies (uniquify_valuation_for (ContextSet.levels cs) true v) (ContextSet.constraints cs).
Proof.
  cbv [satisfies UnivConstraintSet.For_all uniquify_valuation_for].
  intros H x Hi; specialize (H _ ltac:(eapply ConstraintSet_In__declare_and_uniquify_and_combine_levels_1__0, Hi)).
  destruct x as [[l []] r]; cbn in *;
    inversion H; clear H; subst; constructor.
  all: destruct l, r; assumption.
Qed.

Lemma satisfies_declare_and_uniquify_and_combine_levels_1_1 {cs cstr v}
  : satisfies v (ContextSet.constraints cs)
    -> satisfies (ununiquify_valuation 2 v) (ContextSet.constraints (declare_and_uniquify_and_combine_levels (cs, cstr)).1).
Proof.
  cbv [satisfies UnivConstraintSet.For_all ununiquify_valuation].
  intros H x Hi; specialize (H _ ltac:(eapply ConstraintSet_In__declare_and_uniquify_and_combine_levels_1__1, Hi)).
  destruct x as [[l []] r]; cbn in *;
    inversion H; clear H; subst; constructor.
  all: destruct l, r; assumption.
Qed.

Lemma satisfies_declare_and_uniquify_and_combine_levels_2_0 {cs cstr v}
  : satisfies v (declare_and_uniquify_and_combine_levels (cs, cstr)).2
    -> satisfies (uniquify_valuation_for (ContextSet.levels cs) false v) cstr.
Proof.
  cbv [satisfies UnivConstraintSet.For_all uniquify_valuation_for].
  intros H x Hi; specialize (H _ ltac:(eapply ConstraintSet_In__declare_and_uniquify_and_combine_levels_2__0, Hi)).
  destruct x as [[l []] r]; cbn in *;
    inversion H; clear H; subst; constructor.
  all: destruct l, r; assumption.
Qed.

Lemma satisfies_declare_and_uniquify_levels_2_1 {cs cstr v}
  : satisfies v cstr
    -> satisfies (ununiquify_valuation 2 v) (declare_and_uniquify_levels (cs, cstr)).2.
Proof.
  cbv [satisfies UnivConstraintSet.For_all uniquify_valuation_for].
  intros H x Hi; specialize (H _ ltac:(eapply ConstraintSet_In__declare_and_uniquify_levels_2__1, Hi)).
  destruct x as [[l []] r]; cbn in *;
    inversion H; clear H; subst; constructor.
  all: destruct l, r; try assumption.
Qed.

Lemma satisfies_combine_valuations {cs cstr v v'}
  (cscstr := declare_and_uniquify_levels (cs, cstr))
  (cscstr' := declare_and_uniquify_and_combine_levels (cs, cstr))
  (cs' := cscstr'.1) (cstr' := cscstr.2) (cstr'' := cscstr'.2)
  (Hv : satisfies v (ContextSet.constraints cs'))
  (Hv' : satisfies v' cstr')
  (Hagree
    : LevelSet.For_all (fun l => val v (uniquify_level_for (ContextSet.levels cs) true l) = val v' (uniquify_level_for (ContextSet.levels cs) false l)) (ContextSet.levels cs))
  (vc := combine_valuations "b"%byte "l"%byte "r"%byte v v v')
  : satisfies vc cstr''
    /\ LevelSet.For_all (fun l => val v l = val vc l) (ContextSet.levels cs').
Proof.
  repeat match goal with H := _ |- _ => subst H end.
  cbv [satisfies UnivConstraintSet.For_all LevelSet.For_all combine_valuations val Level.Evaluable ContextSet.constraints ContextSet.levels declare_and_uniquify_and_combine_levels declare_and_uniquify_levels] in *;
    cbn [fst snd valuation_poly valuation_mono] in *.
  revert Hv Hv' Hagree.
  progress repeat setoid_rewrite UnivConstraintSet.union_spec.
  progress repeat setoid_rewrite LevelSet_In_fold_add.
  progress repeat setoid_rewrite ConstraintSet_In_fold_add.
  progress repeat setoid_rewrite ConstraintSetFact.empty_iff.
  progress repeat setoid_rewrite LevelSet.singleton_spec.
  cbv [LevelSet.Exists UnivConstraintSet.Exists uniquify_constraint_for uniquify_constraint uniquify_level_for uniquify_level].
  intros.
  split.
  2: intro x; specialize (Hagree (ununiquify_level 2 x)).
  2: cbv [ununiquify_level ununiquify_level_level ununiquify_level_var] in *.
  all: repeat first [ progress intros
                    | progress subst
                    | progress rdest
                    | progress destruct_head'_False
                    | progress destruct_head'_or
                    | progress destruct_head'_ex
                    | progress specialize_by_assumption
                    | progress cbv beta iota in *
                    | reflexivity
                    | match goal with
                      | [ H : forall x, _ \/ _ -> _ |- _ ]
                        => pose proof (fun x H' => H x (or_introl H'));
                           pose proof (fun x H' => H x (or_intror H'));
                           clear H
                      | [ H : _ \/ _ -> _ |- _ ]
                        => pose proof (fun H' => H (or_introl H'));
                           pose proof (fun H' => H (or_intror H'));
                           clear H
                      | [ H : forall x, ex _ -> _ |- _ ]
                        => specialize (fun x x' H' => H x (ex_intro _ x' H'))
                      | [ H : ex _ -> _ |- _ ]
                        => specialize (fun x' H' => H (ex_intro _ x' H'))
                      | [ H : forall x x', _ /\ x = @?f x' -> _ |- _ ]
                        => specialize (fun x' H' => H _ x' (conj H' eq_refl))
                      | [ H : forall x, _ /\ _ = _ -> _ |- _ ]
                        => specialize (fun H' => H _ (conj H' eq_refl))
                      | [ H : forall x, x = _ -> _ |- _ ]
                        => specialize (H _ eq_refl)
                      | [ H : forall x, False -> _ |- _ ] => clear H
                      end ].
  all: repeat first [ progress cbv [uniquify_level_level uniquify_level_var] in *
                    | congruence
                    | lia
                    | progress subst
                    | match goal with
                      | [ H : Level.lvar _ = Level.lvar _ |- _ ] => inversion H; clear H
                      | [ H : Level.level _ = Level.level _ |- _ ] => inversion H; clear H
                      | [ H : (@eqb ?T ?R ?x ?y) = true |- _ ]
                        => destruct (@eqb_spec T R x y)
                      | [ H : (@eqb ?T ?R ?x ?y) = false |- _ ]
                        => destruct (@eqb_spec T R x y)
                      end
                    | progress destruct ? ].
  all: repeat first [ progress rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_mul in *
                    | progress change (Z.of_nat 3) with 3%Z in *
                    | progress change (?n mod 3)%Z with n in *
                    | match goal with
                      | [ H : context[((?x * ?y + ?z) mod ?y)%Z] |- _ ]
                        => rewrite (Z.add_comm (x * y) z) in *
                      end
                    | progress rewrite ?Z_mod_plus_full in *
                    | lia ].
  all: repeat match goal with
         | [ H : LevelSet.In _ _ |- _ ]
           => progress specialize_all_ways_under_binders_by exact H
         | [ H : UnivConstraintSet.In _ _ |- _ ]
           => progress specialize_all_ways_under_binders_by exact H
         end.
  all: repeat first [ progress subst
                    | assumption
                    | progress cbv [val Level.Evaluable] in *
                    | progress cbn [fst snd valuation_mono valuation_poly] in *
                    | progress destruct_head_hnf' prod
                    | match goal with
                      | [ H : satisfies0 _ _ |- _ ] => inversion H; clear H; constructor
                      end ].
  all: repeat first [ progress cbv [uniquify_level_level uniquify_level_var] in *
                    | rewrite eqb_refl
                    | assumption
                    | match goal with
                      | [ H : ?x = true, H' : context[match ?x with _ => _ end] |- _ ]
                        => rewrite H in H'
                      | [ H : ?x = false, H' : context[match ?x with _ => _ end] |- _ ]
                        => rewrite H in H'
                      | [ |- context[LevelSet.mem ?l ?x] ]
                        => let H := fresh in
                           pose proof (@LevelSetFact.mem_2 x l) as H;
                           destruct (LevelSet.mem l x) eqn:?;
                             try (specialize (H eq_refl);
                                  specialize_all_ways_under_binders_by exact H)
                      | [ H : LevelSet.mem ?x ?l = true |- _ ]
                        => unique pose proof (@LevelSetFact.mem_2 _ _ H);
                           let H' := match goal with H' : LevelSet.In x l |- _ => H' end in
                           specialize_all_ways_under_binders_by exact H'
                      end ].
  all: repeat first [ progress cbv beta iota in *
                    | rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul
                    | progress change (Z.of_nat 3) with 3%Z
                    | rewrite Z.add_comm, Z_mod_plus_full
                    | rewrite eqb_refl
                    | assumption
                    | lia
                    | match goal with
                      | [ |- context[(?x == ?y)] ]
                        => change (x == y) with false
                      end ].
Qed.

Lemma consistent_extension_on_iff_declare_and_uniquify_and_combine_levels cs cstr
  : @consistent_extension_on cs cstr
    <-> @consistent_extension_on (declare_and_uniquify_and_combine_levels (cs, cstr)).1 (declare_and_uniquify_and_combine_levels (cs, cstr)).2.
Proof.
  cbv [consistent_extension_on].
  split; intros H v Hs.
  { specialize (H _ (satisfies_declare_and_uniquify_and_combine_levels_1_0 Hs)).
    destruct H as [v' [H0 H1]].
    apply (@satisfies_declare_and_uniquify_levels_2_1 cs cstr) in H0.
    eexists; eapply satisfies_combine_valuations; try eassumption.
    revert H1.
    cbv [LevelSet.For_all ununiquify_valuation uniquify_valuation_for uniquify_valuation val Level.Evaluable uniquify_level_for uniquify_level].
    cbn [valuation_mono valuation_poly].
    intros H1 x Hx; specialize (H1 x Hx); revert H1.
    destruct x; try lia.
    all: first [ rewrite ununiquify_level_level__uniquify_level_level
               | rewrite ununiquify_level_var__uniquify_level_var by lia ].
    all: trivial. }
  { specialize (H _ (satisfies_declare_and_uniquify_and_combine_levels_1_1 Hs)).
    destruct H as [v' [H0 H1]].
    eexists; split;
      [ eapply satisfies_declare_and_uniquify_and_combine_levels_2_0; eassumption | ].
    cbv [LevelSet.For_all] in *.
    intros l Hl; specialize (fun side => H1 _ ltac:(unshelve eapply LevelSet_In_declare_and_uniquify_and_combine_levels_1_1, Hl; exact side)).
    pose proof (H1 true) as H1t.
    pose proof (H1 false) as H1f.
    clear H1.
    cbv [val Level.Evaluable ununiquify_valuation uniquify_level_for uniquify_level uniquify_valuation_for uniquify_valuation] in *.
    destruct l; trivial.
    cbn [valuation_poly valuation_mono] in *.
    rewrite ?ununiquify_level_var__uniquify_level_var in * by lia.
    congruence. }
Qed.

Lemma global_uctx_invariants__declare_and_uniquify_and_combine_levels cs cstr
  : global_uctx_invariants (declare_and_uniquify_and_combine_levels (cs, cstr)).1.
Proof.
  pose proof (levels_of_cs_spec (ContextSet.constraints cs)).
  pose proof (levels_of_cs_spec cstr).
  cbv [declare_and_uniquify_levels]; cbn [fst snd].
  cbv [uGraph.global_uctx_invariants uGraph.uctx_invariants UnivConstraintSet.For_all declared_univ_cstr_levels] in *; cbn [fst snd ContextSet.levels ContextSet.constraints] in *.
  repeat first [ progress subst
               | progress cbv [LevelSet.Exists UnivConstraintSet.Exists uniquify_constraint_for uniquify_constraint uniquify_level_for] in *
               | rewrite !LevelSet_In_fold_add
               | rewrite !ConstraintSet_In_fold_add
               | rewrite !LevelSet.singleton_spec
               | rewrite ConstraintSetFact.empty_iff
               | setoid_rewrite LevelSet_In_fold_add
               | setoid_rewrite ConstraintSet_In_fold_add
               | setoid_rewrite LevelSet.singleton_spec
               | setoid_rewrite ConstraintSetFact.empty_iff
               | match goal with
                 | [ H : (_, _) = (_, _) |- _ ] => inv H
                 | [ H : forall x : UnivConstraintSet.elt, _ |- _ ]
                   => specialize (fun a b c => H ((a, b), c))
                 end
               | solve [ eauto ]
               | progress rdest
               | progress destruct_head'_ex
               | progress split_and
               | progress intros
               | progress destruct ?
               | progress destruct_head'_or ].
Qed.

Lemma consistent_extension_on_iff_subgraph_helper cs cstr G G'
  (cscstr := declare_and_uniquify_and_combine_levels (cs, cstr))
  (cs' := cscstr.1) (cstr' := cscstr.2)
  (cf := config.default_checker_flags) (lvls := levels_of_cscs cs' cstr')
  (HG : gc_of_uctx cs' = Some G)
  (HG' : gc_of_uctx (lvls, cstr') = Some G')
  : subgraph (make_graph G) (make_graph G').
Proof.
  repeat first [ progress cbv [gc_of_uctx monad_utils.bind monad_utils.ret monad_utils.option_monad] in *
               | progress cbn [fst snd] in *
               | progress subst
               | progress destruct ?
               | match goal with
                 | [ H : Some ?x = Some ?y |- _ ] => assert (x = y) by congruence; clear H
                 end
               | congruence ].
  repeat match goal with H := _ |- _ => subst H end.
  split; try reflexivity;
    cbv [levels_of_cscs ContextSet.levels uGraph.wGraph.E make_graph uGraph.wGraph.V];
    cbn [fst snd] in *;
    try solve [ clear; LevelSetDecide.fsetdec ];
    [].
  all: lazymatch goal with
       | [ |- EdgeSet.Subset _ _ ] => idtac
       end.
  intro;
    rewrite !add_cstrs_spec, !add_level_edges_spec, !EdgeSetFact.empty_iff;
    repeat setoid_rewrite VSet.union_spec.
  all: repeat first [ intro
                    | progress destruct_head'_or
                    | progress destruct_head'_ex
                    | progress destruct_head'_and
                    | progress subst
                    | exfalso; assumption
                    | progress rewrite ?@gc_of_constraint_iff in * by eassumption
                    | progress cbv [UnivConstraintSet.Exists on_Some] in *
                    | progress destruct ?
                    | solve [ eauto 6 ] ].
  all: [ > ].
  left; eexists; split; [ reflexivity | ].
  all: repeat first [ intro
                    | progress destruct_head'_or
                    | progress destruct_head'_ex
                    | progress destruct_head'_and
                    | progress subst
                    | exfalso; assumption
                    | progress rewrite ?@gc_of_constraint_iff in * by eassumption
                    | progress cbv [UnivConstraintSet.Exists on_Some] in *
                    | progress destruct ?
                    | solve [ eauto 6 ] ].
  eexists; split;
    [ | match goal with H : _ |- _ => rewrite H; eassumption end ].
  cbv [declare_and_uniquify_and_combine_levels ContextSet.constraints] in *; cbn [fst snd] in *.
  ConstraintSetDecide.fsetdec.
Qed.

Lemma consistent_extension_on_iff cs cstr
  (cscstr := declare_and_uniquify_and_combine_levels (cs, cstr))
  (cs' := cscstr.1) (cstr' := cscstr.2)
  (cf := config.default_checker_flags) (lvls := levels_of_cscs cs' cstr')
  : @consistent_extension_on cs cstr
    <-> is_true
          match uGraph.is_consistent cs', uGraph.is_consistent (lvls, cstr'),
            uGraph.gc_of_uctx cs', uGraph.gc_of_uctx (lvls, cstr') with
          | false, _, _, _
          | _, _, None, _
            => true
          | _, true, Some G, Some G'
            => uGraph.wGraph.IsFullSubgraph.is_full_extension (uGraph.make_graph G) (uGraph.make_graph G')
          | _, _, _, _ => false
          end.
Proof.
  rewrite consistent_extension_on_iff_declare_and_uniquify_and_combine_levels.
  destruct (levels_of_cscs_spec cs' cstr').
  subst cscstr cs' cstr'.
  cbv zeta; repeat destruct ?; subst.
  let H := fresh in pose proof (fun uctx uctx' G => @uGraph.consistent_ext_on_full_ext _ uctx G (lvls, uctx')) as H; cbn [fst snd] in H; erewrite H; clear H.
  1: reflexivity.
  all: cbn [fst snd ContextSet.constraints] in *.
  all: repeat
         repeat
         first [ match goal with
                 | [ H : _ = Some _ |- _ ] => rewrite H
                 | [ H : _ = None |- _ ] => rewrite H
                 | [ |- _ <-> is_true false ]
                   => cbv [is_true]; split; [ let H := fresh in intro H; contradict H | congruence ]
                 | [ |- _ <-> is_true true ]
                   => split; [ reflexivity | intros _ ]
                 end
               | progress cbv [uGraph.is_graph_of_uctx monad_utils.bind monad_utils.ret monad_utils.option_monad] in *
               | progress cbn [MROption.on_Some fst snd] in *
               | rewrite <- uGraph.is_consistent_spec2
               | progress subst
               | assert_fails (idtac; lazymatch goal with |- ?G => has_evar G end);
                 first [ reflexivity | assumption ]
               | match goal with
                 | [ H : ?T, H' : ~?T |- _ ] => exfalso; apply H', H
                 | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?
                 | [ H : uGraph.gc_of_uctx _ = None |- _ ] => cbv [uGraph.gc_of_uctx] in *
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                 | [ H : Some _ = None |- _ ] => inversion H
                 | [ H : None = Some _ |- _ ] => inversion H
                 | [ H : ?T <-> False |- _ ] => destruct H as [H _]; try change (~T) in H
                 | [ H : ~consistent ?cs |- consistent_extension_on (_, ?cs) _ ]
                   => intros ? ?; exfalso; apply H; eexists; eassumption
                 | [ H : ~consistent (snd ?cs) |- consistent_extension_on ?cs _ ]
                   => intros ? ?; exfalso; apply H; eexists; eassumption
                 | [ H : @uGraph.is_consistent ?cf ?uctx = false |- _ ]
                   => assert (~consistent (snd uctx));
                      [ rewrite <- (@uGraph.is_consistent_spec cf uctx), H; clear H; auto
                      | clear H ]
                 | [ H : @uGraph.gc_of_constraints ?cf ?ctrs = None |- _ ]
                   => let H' := fresh in
                      pose proof (@uGraph.gc_consistent_iff cf ctrs) as H';
                      rewrite H in H';
                      clear H
                 | [ H : @uGraph.is_consistent ?cf ?uctx = true |- _ ]
                   => assert_fails (idtac; match goal with
                                           | [ H' : consistent ?v |- _ ] => unify v (snd uctx)
                                           end);
                      assert (consistent (snd uctx));
                      [ rewrite <- (@uGraph.is_consistent_spec cf uctx), H; clear H; auto
                      | ]
                 end ].
  all: try now apply global_uctx_invariants__declare_and_uniquify_and_combine_levels.
  all: try now eapply @consistent_extension_on_iff_subgraph_helper.
  all: try solve [ repeat first [ progress cbv [consistent consistent_extension_on not] in *
                                | progress intros
                                | progress destruct_head'_ex
                                | progress destruct_head'_and
                                | progress specialize_under_binders_by eassumption
                                | solve [ eauto ] ] ].
Qed.

Definition consistent_extension_on_dec cs cstr : {@consistent_extension_on cs cstr} + {~@consistent_extension_on cs cstr}.
Proof.
  pose proof (@consistent_extension_on_iff cs cstr) as H; cbv beta zeta in *.
  let b := lazymatch type of H with context[is_true ?b] => b end in
  destruct b; [ left; apply H; reflexivity | right; intro H'; apply H in H'; auto ].
Defined.

Definition leq0_universe_n_dec n ϕ u u' : {@leq0_universe_n (uGraph.Z_of_bool n) ϕ u u'} + {~@leq0_universe_n (uGraph.Z_of_bool n) ϕ u u'}.
Proof.
  pose proof (@uGraph.gc_leq0_universe_n_iff config.default_checker_flags (uGraph.Z_of_bool n) ϕ u u') as H.
  pose proof (@uGraph.gc_consistent_iff config.default_checker_flags ϕ).
  cbv [on_Some on_Some_or_None] in *.
  destruct gc_of_constraints eqn:?.
  all: try solve [ left; cbv [consistent] in *; hnf; intros; exfalso; intuition eauto ].
  pose proof (fun G cstr => @uGraph.leqb_universe_n_spec G (LevelSet.union (levels_of_cs ϕ) (LevelSet.union (levels_of_universe u) (levels_of_universe u')), cstr)).
  pose proof (fun x y => @gc_of_constraints_of_uctx config.default_checker_flags (x, y)) as H'.
  pose proof (@is_consistent_spec config.default_checker_flags (levels_of_cs ϕ, ϕ)).
  specialize_under_binders_by eapply gc_levels_declared_union_or.
  specialize_under_binders_by eapply global_gc_uctx_invariants_union_or.
  specialize_under_binders_by (constructor; eapply gc_of_uctx_invariants).
  cbn [fst snd] in *.
  specialize_under_binders_by eapply H'.
  specialize_under_binders_by eassumption.
  specialize_under_binders_by eapply levels_of_cs_spec.
  specialize_under_binders_by reflexivity.
  destruct is_consistent;
    [ | left; now cbv [leq0_universe_n consistent] in *; intros; exfalso; intuition eauto ].
  specialize_by intuition eauto.
  let H := match goal with H : forall (b : bool), _ |- _ => H end in
  specialize (H n u u').
  specialize_under_binders_by (constructor; eapply gc_levels_declared_union_or; constructor; eapply levels_of_universe_spec).
  match goal with H : is_true ?b <-> ?x, H' : ?y <-> ?x |- {?y} + {_} => destruct b eqn:?; [ left | right ] end.
  all: intuition.
Defined.

Definition leq_universe_n_dec cf n ϕ u u' : {@leq_universe_n cf (uGraph.Z_of_bool n) ϕ u u'} + {~@leq_universe_n cf (uGraph.Z_of_bool n) ϕ u u'}.
Proof.
  cbv [leq_universe_n]; destruct (@leq0_universe_n_dec n ϕ u u'); destruct ?; auto.
Defined.

Definition eq0_universe_dec ϕ u u' : {@eq0_universe ϕ u u'} + {~@eq0_universe ϕ u u'}.
Proof.
  pose proof (@eq0_leq0_universe ϕ u u') as H.
  destruct (@leq0_universe_n_dec false ϕ u u'), (@leq0_universe_n_dec false ϕ u' u); constructor; destruct H; split_and; now auto.
Defined.

Definition eq_universe_dec {cf ϕ} u u' : {@eq_universe cf ϕ u u'} + {~@eq_universe cf ϕ u u'}.
Proof.
  cbv [eq_universe]; destruct ?; auto using eq0_universe_dec.
Defined.

Definition eq_sort__dec {univ eq_universe}
           (eq_universe_dec : forall u u', {@eq_universe u u'} + {~@eq_universe u u'})
           s s'
  : {@eq_sort_ univ eq_universe s s'} + {~@eq_sort_ univ eq_universe s s'}.
Proof.
  cbv [eq_sort_]; repeat destruct ?; auto. all: destruct pst; auto.
Defined.

Definition eq_sort_dec {cf ϕ} s s' : {@eq_sort cf ϕ s s'} + {~@eq_sort cf ϕ s s'} := eq_sort__dec eq_universe_dec _ _.

Definition valid_constraints_dec cf ϕ cstrs : {@valid_constraints cf ϕ cstrs} + {~@valid_constraints cf ϕ cstrs}.
Proof.
  pose proof (fun G a b c => uGraph.check_constraints_spec (uGraph.make_graph G) (levels_of_cs2 ϕ cstrs, ϕ) a b c cstrs) as H1.
  pose proof (fun G a b c => uGraph.check_constraints_complete (uGraph.make_graph G) (levels_of_cs2 ϕ cstrs, ϕ) a b c cstrs) as H2.
  pose proof (levels_of_cs2_spec ϕ cstrs).
  cbn [fst snd] in *.
  destruct (consistent_dec ϕ); [ | now left; cbv [valid_constraints valid_constraints0 consistent not] in *; destruct ?; intros; eauto; exfalso; eauto ].
  destruct_head'_and.
  specialize_under_binders_by assumption.
  cbv [uGraph.is_graph_of_uctx MROption.on_Some] in *.
  cbv [valid_constraints] in *; repeat destruct ?; auto.
  { specialize_under_binders_by reflexivity.
    destruct uGraph.check_constraints_gen; specialize_by reflexivity; auto. }
  { rewrite uGraph.gc_consistent_iff in *.
    cbv [uGraph.gc_of_uctx monad_utils.bind monad_utils.ret monad_utils.option_monad MROption.on_Some] in *; cbn [fst snd] in *.
    destruct ?.
    all: try congruence.
    all: exfalso; assumption. }
Defined.

Definition valid_constraints0_dec ϕ ctrs : {@valid_constraints0 ϕ ctrs} + {~@valid_constraints0 ϕ ctrs}
  := @valid_constraints_dec config.default_checker_flags ϕ ctrs.

Definition is_lSet_dec cf ϕ s : {@is_lSet cf ϕ s} + {~@is_lSet cf ϕ s}.
Proof.
  apply eq_sort_dec.
Defined.

Definition is_allowed_elimination_dec cf ϕ allowed u : {@is_allowed_elimination cf ϕ allowed u} + {~@is_allowed_elimination cf ϕ allowed u}.
Proof.
  cbv [is_allowed_elimination is_true]; destruct ?; auto;
    try solve [ repeat decide equality ].
  destruct (@is_lSet_dec cf ϕ u), Sort.is_propositional; intuition auto.
Defined.
