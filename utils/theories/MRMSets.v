From Stdlib.Structures Require Import Orders.
From Stdlib.MSets Require Import MSetInterface MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From MetaRocq.Utils Require Import MRReflect.
From Equations.Prop Require Import Classes.

Module Type IsLeibniz (Import T : Eq).
  Parameter eq_leibniz : forall x y, eq x y -> x = y.
End IsLeibniz.

Module UsualIsLeibniz (Import T : UsualEq) <: IsLeibniz T.
  Lemma eq_leibniz x y : eq x y -> x = y.
  Proof. exact id. Qed.
End UsualIsLeibniz.

Module Type IsLtIrrel (Import T : EqLt).
  Parameter lt_irrel : forall x y (p q : T.lt x y), p = q.
End IsLtIrrel.

Module Export MSets.
  Module Type UsualSets <: Sets.
    Declare Module E : UsualOrderedType.
    Include SetsOn E.
  End UsualSets.

  Module Type WDecideOnSig (E : DecidableType) (M : WSetsOn E) := Nop <+ WDecideOn E M.
  Module Type WDecideSig (M : WSets) := Nop <+ WDecide M.
  Module Type DecideSig (M : WSets) := Nop <+ Decide M.

  Module Type WFactsOnSig (E : DecidableType) (M : WSetsOn E) := Nop <+ WFactsOn E M.
  Module Type WFactsSig (M : WSets) := Nop <+ WFacts M.
  Module Type FactsSig (M : WSets) := Nop <+ Facts M.

  Module Type WPropertiesOnSig (E : DecidableType) (M : WSetsOn E) := Nop <+ WPropertiesOn E M.
  Module Type WPropertiesSig (M : WSets) := Nop <+ WProperties M.
  Module Type PropertiesSig (M : WSets) := Nop <+ Properties M.
  Module Type OrdPropertiesSig (M : Sets) := Nop <+ OrdProperties M.

  Module WExtraPropertiesOn (E : DecidableType) (Import W : WSetsOn E) (WProperties : WPropertiesOnSig E W).

    Definition For_all_alt (P : elt -> Prop) (s : t) : Prop
    := List.Forall P (elements s).
    #[local] Hint Extern 1 (E.eq _ _) => reflexivity : core.
    Lemma For_all_alt_iff {P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {s}
      : For_all_alt P s <-> For_all P s.
    Proof using Type.
      cbv [For_all_alt For_all].
      setoid_rewrite WProperties.FM.elements_iff.
      induction (elements s) as [|x xs IH].
      { split; solve [ constructor | inversion 2 ]. }
      { setoid_rewrite Forall_cons_iff; setoid_rewrite InA_cons; setoid_rewrite IH.
        intuition auto.
        eapply P_Proper; (idtac + symmetry); eassumption. }
    Qed.
    Lemma For_all_forall_iff {P s} : (For_all P s) <-> (forall v, In v s -> P v).
    Proof using Type. reflexivity. Qed.
    Lemma For_all_forall2_iff {P s} : (For_all (fun v1 => For_all (P v1) s) s) <-> (forall v1 v2, In v1 s -> In v2 s -> P v1 v2).
    Proof using Type. cbv [For_all]; intuition eauto. Qed.

    Definition Exists_alt (P : elt -> Prop) (s : t) : Prop
      := List.Exists P (elements s).
    Lemma Exists_alt_iff {P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {s}
      : Exists_alt P s <-> Exists P s.
    Proof.
      cbv [Exists_alt Exists].
      setoid_rewrite WProperties.FM.elements_iff.
      induction (elements s) as [|x xs IH].
      { split; try solve [ constructor | inversion 1 | intros [x [H H']]; inversion H ]. }
      { setoid_rewrite Exists_cons; setoid_rewrite InA_cons; setoid_rewrite IH.
        firstorder intuition auto. }
    Qed.
    Definition Exists_dec {P s} (P_dec : forall x, {P x} + {~P x}) {P_Proper : Proper (E.eq ==> Basics.impl) P} : {Exists P s} + {~Exists P s}.
    Proof.
      destruct (List.Exists_dec P (elements s) P_dec) as [H|H]; [ left | right ]; revert H.
      { intro H; apply Exists_alt_iff, H. }
      { intros H H'; apply H, Exists_alt_iff, H'. }
    Defined.
  End WExtraPropertiesOn.

  Module Type WExtraPropertiesOnSig (E : DecidableType) (W : WSetsOn E) (WProperties : WPropertiesOnSig E W) := Nop <+ WExtraPropertiesOn E W WProperties.

  Module ExtraOrdProperties (Import M : Sets) (Import MOrdProperties : OrdPropertiesSig M).
    Module P := WExtraPropertiesOn M.E M MOrdProperties.P.

    Definition above x s : bool := for_all (fun y => if ME.lt_dec y x then true else false) s.
    Definition below x s : bool := for_all (fun y => if ME.lt_dec x y then true else false) s.
    Lemma above_spec x s : above x s = true <-> Above x s.
    Proof.
      cbv [Above above].
      rewrite for_all_spec
        by (intros ?? H; repeat (let H' := fresh in destruct ME.lt_dec as [H'|H']; rewrite ?H in H'); try reflexivity; tauto).
      cbv [For_all].
      split; intros H y H'; generalize (H y H'); destruct ME.lt_dec; try reflexivity; eauto; congruence.
    Qed.
    Lemma below_spec x s : below x s = true <-> Below x s.
    Proof.
      cbv [Below below].
      rewrite for_all_spec
        by (intros ?? H; repeat (let H' := fresh in destruct ME.lt_dec as [H'|H']; rewrite ?H in H'); try reflexivity; tauto).
      cbv [For_all].
      split; intros H y H'; generalize (H y H'); destruct ME.lt_dec; try reflexivity; eauto; congruence.
    Qed.
  End ExtraOrdProperties.

  Module Type ExtraOrdPropertiesSig (M : Sets) (MOrdProperties : OrdPropertiesSig M) := Nop <+ ExtraOrdProperties M MOrdProperties.
End MSets.

Module MSetAVL.
  Module Type MakeSig (T : OrderedType) := Nop <+ MSetAVL.Make T.

  Module Decide (T : OrderedType) (M : MSetAVL.MakeSig T).
    Module Raw.
      Scheme Induction for M.Raw.tree Sort Type.
      Scheme Induction for M.Raw.tree Sort Set.
      Scheme Induction for M.Raw.tree Sort Prop.
      Scheme Case for M.Raw.tree Sort Type.
      Scheme Case for M.Raw.tree Sort Prop.
      Scheme Minimality for M.Raw.tree Sort Type.
      Scheme Minimality for M.Raw.tree Sort Set.
      Scheme Minimality for M.Raw.tree Sort Prop.

      Fixpoint lt_tree_dec x t : { M.Raw.lt_tree x t } + {~ M.Raw.lt_tree x t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node z l n r
                 => match T.compare n x as c, lt_tree_dec x l, lt_tree_dec x r return CompareSpec _ _ _ c -> _ with
                    | Lt, left p2, left p3 => fun pfc => left _
                    | _, right pf, _ => fun pfc => right _
                    | _, _, right pf => fun pfc => right _
                    | _, _, _ => fun pfc => right _
                    end (T.compare_spec _ _)
               end;
          try solve [ inversion 1; inversion pfc
                    | inversion 1; inversion pfc; subst; auto;
                      match goal with
                      | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                        => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                      end
                    | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                    | intro f; inversion pfc; eapply M.Raw.MX.lt_irrefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
      Defined.
      Fixpoint gt_tree_dec x t : { M.Raw.gt_tree x t } + {~ M.Raw.gt_tree x t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node z l n r
                 => match T.compare n x as c, gt_tree_dec x l, gt_tree_dec x r return CompareSpec _ _ _ c -> _ with
                    | Gt, left p2, left p3 => fun pfc => left _
                    | _, right pf, _ => fun pfc => right _
                    | _, _, right pf => fun pfc => right _
                    | _, _, _ => fun pfc => right _
                    end (T.compare_spec _ _)
               end;
          try solve [ inversion 1; inversion pfc
                    | inversion 1; inversion pfc; subst; auto;
                      match goal with
                      | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                        => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                      end
                    | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                    | intro f; inversion pfc; eapply M.Raw.MX.lt_irrefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
      Defined.
      Fixpoint bst_dec t : { M.Raw.bst t } + {~ M.Raw.bst t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node z l n r
                 => match bst_dec l, bst_dec r, lt_tree_dec n l, gt_tree_dec n r with
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
    End Raw.
  End Decide.

  Module Type DecideSig (T : OrderedType) (M : MSetAVL.MakeSig T) := Nop <+ Decide T M.

  Module LtIrrel (T : OrderedType) (M : MSetAVL.MakeSig T) (TIrrel : IsLtIrrel T).
    Module Raw.
      (* assumes funext :-( *)
      Lemma lt_tree_irrel x y (p q : M.Raw.lt_tree x y) : p = q.
      Proof.
        hnf in p, q.
        apply FunctionalExtensionality.functional_extensionality_dep; intro.
        apply FunctionalExtensionality.functional_extensionality_dep; intro.
        apply TIrrel.lt_irrel.
      Qed.

      Lemma gt_tree_irrel x y (p q : M.Raw.gt_tree x y) : p = q.
      Proof.
        hnf in p, q.
        apply FunctionalExtensionality.functional_extensionality_dep; intro.
        apply FunctionalExtensionality.functional_extensionality_dep; intro.
        apply TIrrel.lt_irrel.
      Qed.
      Definition invert_bst {t} (x : M.Raw.bst t)
        := match x as x in M.Raw.bst t return match t return M.Raw.bst t -> Prop with
                                              | M.Raw.Leaf => fun b => M.Raw.BSLeaf = b
                                              | M.Raw.Node c l x r
                                                => fun b
                                                   => { bl : _ | { br : _ | { ltl : _ | { gtr : _  | M.Raw.BSNode c x l r bl br ltl gtr = b }}}}
                                              end x with
           | M.Raw.BSLeaf => eq_refl
           | M.Raw.BSNode c x l r bl br ltl gtr => exist bl (exist br (exist ltl (exist gtr eq_refl)))
           end.
      Lemma bst_irrel t (x y : M.Raw.bst t) : x = y.
      Proof.
        induction t.
        { pose proof (invert_bst x) as Hx.
          pose proof (invert_bst y) as Hy.
          cbn in *; subst; reflexivity. }
        { pose proof (invert_bst x) as Hx.
          pose proof (invert_bst y) as Hy.
          cbn in *; subst.
          repeat match goal with H : sig _ |- _ => destruct H end.
          subst; f_equal; eauto using lt_tree_irrel, gt_tree_irrel. }
      Qed.
    End Raw.
  End LtIrrel.

  Module Type LtIrrelSig (T : OrderedType) (M : MSetAVL.MakeSig T) (TIrrel : IsLtIrrel T) := Nop <+ LtIrrel T M TIrrel.

  Module DecideWithLeibniz (T : OrderedType) (M : MSetAVL.MakeSig T) (L : IsLeibniz T) (I : IsLtIrrel T) (Import D : DecideSig T M) (Import MI : LtIrrelSig T M I).
    Module Raw.
      Import D.Raw.
      Definition tree_dec (x y : M.Raw.tree) : {x = y} + {x <> y}.
      Proof.
        decide equality; try apply BinInt.Z.eq_dec.
        let H := fresh in
        lazymatch goal with
        | [ |- {?x = ?y :> T.t} + {_} ]
          => destruct (T.eq_dec x y) as [H|H]
        end;
        [ left; apply L.eq_leibniz in H; assumption
        | right; clear -H; abstract (intro; subst; apply H; reflexivity) ].
      Defined.
      #[global] Instance tree_EqDec : EqDec M.Raw.tree := { eq_dec := tree_dec }.
      #[global] Instance t_EqDec : EqDec M.Raw.t := _.
    End Raw.
    Import M.
    Definition t_dec (x y : M.t) : {x = y} + {x <> y}.
    Proof.
      destruct (Raw.tree_dec x.(this) y.(this)); [ left | right ].
      { destruct x, y; cbn in *; subst; apply f_equal.
        apply Raw.bst_irrel. }
      { abstract congruence. }
    Defined.
    #[global] Instance t_EqDec : EqDec M.t := { eq_dec := t_dec }.
  End DecideWithLeibniz.

  Module Type DecideWithLeibnizSig (T : OrderedType) (M : MSetAVL.MakeSig T) (L : IsLeibniz T) (I : IsLtIrrel T) (D : DecideSig T M) (MI : LtIrrelSig T M I) := Nop <+ DecideWithLeibniz T M L I D MI.
End MSetAVL.

Module MSetList.
  Module Type MakeSig (T : OrderedType) := Nop <+ MSetList.Make T.

  Module Type MakeWithLeibnizSig (X : OrderedTypeWithLeibniz) := Nop <+ MakeWithLeibniz X.
End MSetList.
