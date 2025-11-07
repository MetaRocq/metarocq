(* Distributed under the terms of the MIT license. *)
Set Warnings "-notation-overridden".
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import Checker All.
From MetaRocq.Translations Require Import translation_utils MiniHoTT_paths.

Import MRMonadNotation.

Reserved Notation "'tsl_ty_param'".

Unset MetaRocq Strict Unquote Universe Mode.

MetaRocq Quote Definition tSigma := @sigT.
MetaRocq Quote Definition tPair := @existT.
Definition pair (typ1 typ2 t1 t2 : term) : term
  := tApp tPair [ typ1 ; typ2 ; t1 ; t2].
Definition pack (t u : term) : term
  := tApp tSigma [ t ; u ].
MetaRocq Run (t <- tmQuote (@sigT) ;;
            match t with
            | tInd i _ => tmDefinition "sigma_ind" i
            | _ => tmFail "bug"
            end).
Definition proj1 (t : term) : term
  := tProj (mkProjection sigma_ind 2 0) t.
Definition proj2 (t : term) : term
  := tProj (mkProjection sigma_ind 2 (S 0)) t.
Definition proj (b : bool) (t : term) : term
  := tProj (mkProjection sigma_ind 2 (if b then 0 else S 0)) t.

Definition refresh_universe u :=
  if Universe.is_level u then u else fresh_universe.

Definition refresh_sort_universe := Sort.map refresh_universe.

Fixpoint refresh_universes (t : term) {struct t} :=
  match t with
  | tSort s => tSort (refresh_sort_universe s)
  | tProd na b t => tProd na b (refresh_universes t)
  | tLetIn na b t' t => tLetIn na b t' (refresh_universes t)
  | _ => t
  end.

Local Instance tit : config.checker_flags
  := config.type_in_type.
#[export] Existing Instance Checker.default_fuel.

(* if b it is the first translation, else the second *)
Fixpoint tsl_rec (fuel : nat) (Σ : global_env_ext) (E : tsl_table) (Γ : context)
         (b : bool) (t : term) {struct fuel} : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel n => ret (proj b (tRel n))

  | tSort s =>
    if b then ret (tSort s)
    else ret (tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s)))

  | tCast t c A => if b then
                    t1 <- tsl_rec fuel Σ E Γ true t ;;
                    A1 <- tsl_rec fuel Σ E Γ true A ;;
                    ret (tCast t1 c A1)
                  else
                    t1 <- tsl_rec fuel Σ E Γ true t ;;
                    t2 <- tsl_rec fuel Σ E Γ false t ;;
                    A2 <- tsl_rec fuel Σ E Γ false A ;;
                    ret (tCast t2 c (tApp A2 [t1]))

  | tProd n A B =>
    if b then
      A' <- tsl_ty_param fuel Σ E Γ A ;;
         B1 <- tsl_rec fuel Σ E (Γ ,, vass n A) true B ;;
         ret (tProd n A' B1)
    else
      A' <- tsl_ty_param fuel Σ E Γ A ;;
      B1 <- tsl_rec fuel Σ E (Γ ,, vass n A) true B ;;
      B2 <- tsl_rec fuel Σ E (Γ ,, vass n A) false B ;;
      ret (tLambda (nNamed "f") (tProd n A' B1)
                   (tProd n (lift 1 0 A')
                          (tApp (lift 1 1 B2)
                                [tApp (tRel 1) [tRel 0]])))

  | tLambda n A t => A' <- tsl_ty_param fuel Σ E Γ A ;;
                    t' <- tsl_rec fuel Σ E (Γ ,, vass n A) b t ;;
                    ret (tLambda n A' t')

  | tLetIn n t A u => t' <- tsl_term fuel Σ E Γ t ;;
                     A' <- tsl_ty_param fuel Σ E Γ A ;;
                     u' <- tsl_rec fuel Σ E (Γ ,, vdef n t A) b u ;;
                     ret (tLetIn n t' A' u')

  | tApp t u => t' <- tsl_rec fuel Σ E Γ b t ;;
               u' <- monad_map (tsl_term fuel Σ E Γ) u ;;
               ret (tApp t' u')

  | tConst _ _ as t
  | tInd _ _ as t
  | tConstruct _ _ _ as t => t' <- tsl_term fuel Σ E Γ t ;;
                            ret (proj b t')
  | _ => raise TranslationNotHandeled
  end
  end

with tsl_term  (fuel : nat) (Σ : global_env_ext) (E : tsl_table) (Γ : context)
               (t : term) {struct fuel} : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel n => ret (tRel n)

  | tSort s =>
    ret (pair (tSort (sType fresh_universe))
              (tLambda (nNamed "A") (tSort (sType fresh_universe)) (tProd nAnon (tRel 0) (tSort (sType fresh_universe))))
              (tSort s)
              (tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s))))

  | tCast t c A => t' <- tsl_term fuel Σ E Γ t ;;
                  A' <- tsl_ty_param fuel Σ E Γ A ;;
                  ret (tCast t' c A')

  | tConst s univs => lookup_tsl_table' E (ConstRef s)
  | tInd i univs => lookup_tsl_table' E (IndRef i)
  | tConstruct i n univs => lookup_tsl_table' E (ConstructRef i n)
  | t => match infer' Σ Γ t with
         | Checked typ => let typ := refresh_universes typ in
                         t1 <- tsl_rec fuel Σ E Γ true t ;;
                         t2 <- tsl_rec fuel Σ E Γ false t ;;
                         typ1 <- tsl_rec fuel Σ E Γ true typ ;;
                         typ2 <- tsl_rec fuel Σ E Γ false typ ;;
                         ret (pair typ1 typ2 t1 t2)
        | TypeError t => raise (TypingError t)
        end
  end
  end
where "'tsl_ty_param'" := (fun fuel Σ E Γ t =>
                        t1 <- tsl_rec fuel Σ E Γ true t ;;
                        t2 <- tsl_rec fuel Σ E Γ false t ;;
                        ret (pack t1 t2)).



#[export] Instance tsl_param : Translation
  := {| tsl_id := tsl_ident ;
        tsl_tm := fun ΣE => tsl_term fuel (fst ΣE) (snd ΣE) [] ;
        tsl_ty := Some (fun ΣE => tsl_ty_param fuel (fst ΣE) (snd ΣE) []) ;
        tsl_ind := todo "tsl" |}.



Notation "'TYPE'" := ({ A : Type & A -> Type}).
Notation "'El' A" := (@sigT A.1 A.2) (at level 20).


Definition Ty := Type.
MetaRocq Run (Translate emptyTC "Ty").
Unset Universe Checking.
Check Tyᵗ : El Tyᵗ.



MetaRocq Run (TC <- ImplementExisting emptyTC "sigT" ;;
                     tmDefinition "TC" TC).
Next Obligation.
  unshelve econstructor.
(*   - intros A B. refine (sigma (El A) (fun x => sigma (B.1 x) (B.2 x))). *)
(*   - cbn. intros A B X. exact unit.  *)
(* Defined. *)
  - intros A B. refine (@sigT (El A) B.1).
  - cbn; intros A B. refine (fun x => B.2 x.1 x.2).
Defined.

MetaRocq Run (TC <- ImplementExisting TC "existT" ;;
                     tmDefinition "TC'" TC).
Next Obligation.
  unshelve econstructor.
(*   - intros A B x y. econstructor. exact y. *)
(*   - intros A B π1 H. constructor.  *)
(* Defined. *)
  - intros A B x y. econstructor. exact y.1.
  - cbn; intros A B x y. exact y.2.
Defined.

(*
Time MetaRocq Run (TC <- ImplementExisting TC' "sigT_ind" ;;
                          tmDefinition "TC''" TC).
Next Obligation.
  unshelve econstructor.
(*   - intros A B P [X1 X2] [s []]. apply X1. *)
(*   - intros A B P [X1 X2] [s []]. apply X2. *)
(* Defined. *)
  - intros A B P [X1 X2] [s s']. apply (X1 s.1 (s.2; s')).
  - intros A B P [X1 X2] [s s']. apply (X2 s.1 (s.2; s')).
Defined.


MetaRocq Run (TC <- ImplementExisting TC'' "paths" ;;
                     tmDefinition "TC3" TC).
Next Obligation.
  unshelve econstructor.
  - intros A x y. refine (x.1 = y.1).
  - cbn; intros A x y p. refine (p # x.2 = y.2).
Defined.


MetaRocq Run (TC <- ImplementExisting TC3 "idpath" ;;
                     tmDefinition "TC4" TC).
Next Obligation.
  unshelve econstructor; reflexivity.
Defined.

MetaRocq Run (TC <- ImplementExisting TC4 "paths_ind" ;;
                     tmDefinition "TC5" TC).
Next Obligation.
  unshelve econstructor.
  - intros A [x x'] P X [y y'] [p q]. cbn in *. destruct p, q; cbn.
    exact X.1.
  - intros A [x x'] P X [y y'] [p q]. cbn in *. destruct p, q; cbn.
    exact X.2.
Defined.


Definition Funext :=
  forall A (B : A -> Type) (f g : forall x, B x), (forall x, paths (f x) (g x)) -> paths f g.

MetaRocq Run (Translate TC5 "Funext").

Definition Funext_fullFunext : Funext -> forall A B f g, IsEquiv (@apD10 A B f g).
Admitted.

Goal Funext -> El Funextᵗ.
  simpl. intro H. assert (H0 := Funext_fullFunext H); clear H.
  rename H0 into H.
  unshelve econstructor.
  - intros A B f g X. apply H. exact X.1.
  - intros A B f g [X1 X2]; cbn in *.
    apply H. intro x. rewrite transport_forall_constant.
    specialize (X2 x).
    refine (_ @ X2).
    rewrite transport_compose.
    eapply ap10. eapply ap.
    rewrite ap_apply_lD. now rewrite eisretr.
Defined.


Definition FALSE := forall X, X.
MetaRocq Run (Translate emptyTC "FALSE").

Proposition consistency_preservation : El FALSEᵗ -> FALSE.
  compute.
  intros [f _] X.
  exact (f (X; fun _ => unit)).
Defined.


Definition UIP := forall A (x y : A) (p q : paths x y), paths p q.

MetaRocq Run (Translate TC5 "UIP").

Proposition uip_preservation : UIP -> El UIPᵗ.
  simpl. intro H. unshelve econstructor.
  - intros A x y p q. apply H.
  - cbn. intros A x y p q.  apply H.
Defined.

Notation " A × B " := (@sigT A (fun _ => B)) : type_scope.

Definition equiv (A B : Type) : Type :=
  exists (f : A -> B) (g : B -> A),
    (forall x, paths (g (f x)) x) × (forall x, paths (f (g x)) x).

MetaRocq Run (TC <- ImplementExisting TC5 "False" ;;
                     tmDefinition "TC6" TC).
Next Obligation.
  unshelve econstructor.
  - exact False.
  - intros _. exact False.
Defined.

MetaRocq Run (TC <- Translate TC6 "equiv" ;;
                     tmDefinition "TC7" TC).

(* 244s (~ 4 min) to execute *)
(* Time
MetaRocq Run (H <- Implement TC7 "notUnivalence"
                     (exists A B, (equiv A B) × exists P, P A × ((P B) -> False)) ;;
                     tmPrint "done").
Check "proof".
Next Obligation.
  unshelve econstructor.
  - exists (bool; fun _=> unit).
    exists (unit; fun _=> bool).
    cbn. unshelve econstructor.
    + unshelve econstructor.
      unshelve econstructor.
      exists (fun _ => tt). exact pr1.
      unshelve econstructor.
      exists pr2. exact (fun _ => tt).
      split; [|intros [[] x]; reflexivity].
      unshelve econstructor; [reflexivity|].
      intros [x []]; reflexivity.
      cbn. intros [[] x]; reflexivity.
    + unshelve econstructor.
      exists (fun T => exists (x y : T.1), x = y -> False). exact (fun _ _ => unit).
      cbn; split.
      refine ((true; (false; _)); tt). intro e; inversion e.
      intros [[[] [[] H]] _]. apply H; reflexivity.
  - cbn. intros [[[] [[] H]] _]. apply H; reflexivity.
Defined. *)
*)