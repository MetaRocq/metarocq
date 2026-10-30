From Stdlib.Structures Require Import Equalities Orders OrdersAlt.
From Stdlib.FSets Require Import FMapInterface FMapList FMapAVL FMapFullAVL FMapFacts.
From MetaRocq.Utils Require Import MRReflect MRUtils.
From MetaRocq.Utils.MRTactics Require Import SpecializeUnderBindersBy DestructHead SplitInContext.
From Equations.Prop Require Import Classes.

Module Export FSets.
  Module Type WFacts_funSig (E : DecidableTypeOrig) (M : WSfun E) := Nop <+ WFacts_fun E M.

  Module WFactsExtra_fun (E : DecidableTypeOrig) (Import W : WSfun E) (Import WFacts : WFacts_funSig E W).

    Section with_elt.
      Context {elt : Type}.

      Definition Equiv_alt (eq_elt : elt -> elt -> Prop) m m' :=
        let eq_opt_elt x y := match x, y with
                              | Some x, Some y => eq_elt x y
                              | None, None => True
                              | Some _, None | None, Some _ => False
                              end in
        List.Forall (fun '(k, _) => eq_opt_elt (find k m) (find k m')) (@elements elt m)
        /\ List.Forall (fun '(k, _) => eq_opt_elt (find k m) (find k m')) (@elements elt m').

      Lemma Equiv_alt_iff {eq_elt m m'} : Equiv_alt eq_elt m m' <-> Equiv eq_elt m m'.
      Proof using Type.
        cbv [Equiv Equiv_alt].
        cbv [In] in *.
        setoid_rewrite find_mapsto_iff.
        rewrite !Forall_forall.
        pose proof (@find_o elt m).
        pose proof (@find_o elt m').
        transitivity
          (let eq_opt_elt x y := match x, y with
                                 | Some x, Some y => eq_elt x y
                                 | None, None => True
                                 | Some _, None | None, Some _ => False
                                 end in
           (forall k, In k m -> eq_opt_elt (find k m) (find k m'))
           /\ (forall k, In k m' -> eq_opt_elt (find k m) (find k m'))).
        1: cbv [In]; setoid_rewrite elements_mapsto_iff; setoid_rewrite InA_alt; cbv [eq_key_elt]; cbn [fst snd].
        2: cbv [In]; setoid_rewrite find_mapsto_iff.
        all: repeat (split || intros || destruct_head'_and || split_iff || destruct_head'_prod || destruct_head'_ex || subst).
        all: specialize_dep_under_binders_by eapply ex_intro.
        all: specialize_dep_under_binders_by eapply conj.
        all: specialize_dep_under_binders_by eapply eq_refl.
        all: specialize_dep_under_binders_by eapply pair.
        all: cbn [fst snd] in *.
        all: specialize_all_ways_under_binders_by apply E.eq_refl.
        all: repeat first [ progress destruct_head'_ex
                          | match goal with
                            | [ H : List.In _ _ |- _ ]
                              => progress specialize_under_binders_by exact H
                            | [ H : E.eq _ _ |- _ ]
                              => progress specialize_under_binders_by exact H
                            | [ H : find _ _ = Some _ |- _ ]
                              => progress specialize_under_binders_by exact H
                            end ].
        all: try solve [ repeat destruct ?; subst; try congruence; intuition eauto ].
      Qed.
    End with_elt.
  End WFactsExtra_fun.

  Module Type WFactsExtra_funSig (E : DecidableTypeOrig) (W : WSfun E) (WFacts : WFacts_funSig E W) := Nop <+ WFactsExtra_fun E W WFacts.
End FSets.

Module FMapList.
  Module Type RawSig (T : OrderedTypeOrig) := Nop <+ FMapList.Raw T.
End FMapList.

Module FMapAVL.
  Module Type MakeSig (T : OrderedTypeOrig) := Nop <+ FMapAVL.Make T.

  Module Decide (T : OrderedTypeOrig) (M : FMapAVL.MakeSig T).
    Module Raw.
      Scheme Induction for M.Raw.tree Sort Type.
      Scheme Induction for M.Raw.tree Sort Set.
      Scheme Induction for M.Raw.tree Sort Prop.
      Scheme Case for M.Raw.tree Sort Type.
      Scheme Case for M.Raw.tree Sort Prop.
      Scheme Minimality for M.Raw.tree Sort Type.
      Scheme Minimality for M.Raw.tree Sort Set.
      Scheme Minimality for M.Raw.tree Sort Prop.

      Section with_t.
        Context {elt : Type}.

        Fixpoint lt_tree_dec x t : { @M.Raw.lt_tree elt x t } + {~ @M.Raw.lt_tree elt x t}.
        Proof.
          refine match t with
                 | @M.Raw.Leaf _ => left _
                 | M.Raw.Node l k n r z
                   => match T.compare k x, lt_tree_dec x l, lt_tree_dec x r with
                      | LT p1, left p2, left p3 => left _
                      | _, right pf, _ => right _
                      | _, _, right pf => right _
                      | _, _, _ => right _
                      end
                 end;
            try solve [ inversion 1
                      | inversion 1; subst; auto;
                        match goal with
                        | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                          => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                        end
                      | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                      | intro f; eapply M.Raw.Proofs.MX.lt_antirefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
        Defined.
        Fixpoint gt_tree_dec x t : { @M.Raw.gt_tree elt x t } + {~ @M.Raw.gt_tree elt x t}.
        Proof.
          refine match t with
                 | @M.Raw.Leaf _ => left _
                 | M.Raw.Node l k n r z
                   => match T.compare k x, gt_tree_dec x l, gt_tree_dec x r with
                      | GT p1, left p2, left p3 => left _
                      | _, right pf, _ => right _
                      | _, _, right pf => right _
                      | _, _, _ => right _
                      end
                 end;
            try solve [ inversion 1
                      | inversion 1; subst; auto;
                        match goal with
                        | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                          => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                        end
                      | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                      | intro f; eapply M.Raw.Proofs.MX.lt_antirefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
        Defined.
        Fixpoint bst_dec t : { @M.Raw.bst elt t } + {~ @M.Raw.bst elt t}.
        Proof.
          refine match t with
                 | @M.Raw.Leaf _ => left _
                 | M.Raw.Node l k n r z
                   => match bst_dec l, bst_dec r, lt_tree_dec k l, gt_tree_dec k r with
                      | right pf, _, _, _ => right _
                      | _, right pf, _, _ => right _
                      | _, _, right pf, _ => right _
                      | _, _, _, right pf => right _
                      | left p1, left p2, left p3, left p4 => left _
                      end
                 end;
            try solve [ constructor; assumption
                      | inversion 1; subst; auto ].
        Defined.
      End with_t.
    End Raw.
  End Decide.

  Module Type DecideSig (T : OrderedTypeOrig) (M : FMapAVL.MakeSig T) := Nop <+ Decide T M.
End FMapAVL.
