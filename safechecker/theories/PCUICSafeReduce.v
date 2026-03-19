(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import RelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICGeneration PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICPosition PCUICNormal
     PCUICInversion PCUICSR PCUICSN
     PCUICUtils PCUICReduction PCUICValidity PCUICSafeLemmata
     PCUICConfluence PCUICConversion
     PCUICOnFreeVars PCUICWellScopedCumulativity
     PCUICClassification.

From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfReduction PCUICWfEnv.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations Transparent.
Set Equations With UIP.

(** * Reduction machine for PCUIC without fuel

  We implement the reduction machine of Rocq without relying on fuel.
  Instead we assume strong normalization of the system (for well-typed terms)
  and proceed by well-founded induction.

  Once extracted, this should roughly correspond to the OCaml implementation.

 *)

(* From Program *)
Notation " `  t " := (proj1_sig t) (at level 10, t at next level) : metarocq_scope.

Set Default Goal Selector "!".

Local Set Keyed Unification.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma welltyped_is_closed_context {cf Σ} {wfΣ : wf Σ} {Γ t} :
  welltyped Σ Γ t -> is_closed_context Γ.
Proof.
  intros []. now eapply typing_wf_local in X; fvs.
Qed.
#[global] Hint Resolve welltyped_is_closed_context : fvs.

Lemma welltyped_is_open_term {cf Σ} {wfΣ : wf Σ} {Γ t} :
  welltyped Σ Γ t -> is_open_term Γ t.
Proof.
  intros []; fvs.
Qed.
#[global] Hint Resolve welltyped_is_open_term : fvs.


(* We assume normalization of the reduction.

   We state is as well-foundedness of the reduction.
*)
Section Measure.

  Context {cf : checker_flags} {no : normalizing_flags}.

  Context (flags : RedFlags.t).
  Context (Σ : global_env_ext).

  Definition R_aux Γ :=
    dlexprod (cored Σ Γ) (@posR).

  Definition R Γ u v :=
    R_aux Γ (zip u ; stack_pos (fst u) (snd u))
            (zip v ; stack_pos (fst v) (snd v)).

  Lemma cored_welltyped :
    forall {Γ u v},
      wf Σ -> welltyped Σ Γ u ->
      cored Σ Γ v u ->
      welltyped Σ Γ v.
  Proof using Type.
    intros Γ u v HΣ h r.
    revert h. induction r ; intros h.
    - destruct h as [A HA]. exists A.
      eapply subject_reduction1 ; eassumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A HA]. exists A.
      eapply subject_reduction1 ; eassumption.
  Qed.

  Lemma red_welltyped :
    forall {Γ u v},
      wf Σ -> welltyped Σ Γ u ->
      red (fst Σ) Γ u v ->
      welltyped Σ Γ v.
  Proof using Type.
    intros hΣ Γ u v h r. apply red_cored_or_eq in r.
    destruct r as [r|[]]; [|assumption].
    eapply cored_welltyped ; eauto.
  Qed.


  Derive Signature for Acc.
  Lemma R_positionR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2),
      t1 = t2 ->
      positionR (` p1) (` p2) ->
      R_aux Γ (t1 ; p1) (t2 ; p2).
  Proof using Type.
    intros Γ t1 t2 p1 p2 e h.
    subst. right. assumption.
  Qed.

  Definition Req Γ t t' :=
    t = t' \/ R Γ t t'.

  Lemma Rtrans :
    forall Γ u v w,
      R Γ u v ->
      R Γ v w ->
      R Γ u w.
  Proof using Type.
    intros Γ u v w h1 h2.
    eapply dlexprod_trans.
    - intros ? ? ? ? ?. eapply cored_trans' ; eassumption.
    - eapply posR_trans.
    - eassumption.
    - eassumption.
  Qed.

  Lemma Req_trans :
    forall {Γ}, Transitive (Req Γ).
  Proof using Type.
    intros Γ u v w h1 h2.
    destruct h1.
    - subst. assumption.
    - destruct h2.
      + subst. right. assumption.
      + right. eapply Rtrans ; eassumption.
  Qed.

  Lemma R_to_Req :
    forall {Γ u v},
      R Γ u v ->
      Req Γ u v.
  Proof using Type.
    intros Γ u v h.
    right. assumption.
  Qed.

  Instance Req_refl : forall Γ, Reflexive (Req Γ).
  Proof using Type.
    intros Γ.
    left. reflexivity.
  Qed.

  Lemma R_Req_R :
    forall {Γ u v w},
      R Γ u v ->
      Req Γ v w ->
      R Γ u w.
  Proof using Type.
    intros Γ u v w h1 h2.
    destruct h2.
    - subst. assumption.
    - eapply Rtrans ; eassumption.
  Qed.

End Measure.

(* Added by Julien Forest on 13/11/20 in Rocq stdlib, adapted to subset case by M. Sozeau *)
Section Acc_sidecond_generator.
  Context {A : Type} {R : A -> A -> Prop} {P : A -> Prop}.
  Variable Pimpl : forall x y, P x -> R y x -> P y.
  (* *Lazily* add 2^n - 1 Acc_intro on top of wf.
     Needed for fast reductions using Function and Program Fixpoint
     and probably using Fix and Fix_F_2
   *)
  Fixpoint Acc_intro_generator n (acc : forall t, P t -> Acc R t) : forall t, P t -> Acc R t :=
    match n with
        | O => acc
        | S n => fun x Px =>
                   Acc_intro x (fun y Hy => Acc_intro_generator n (Acc_intro_generator n acc) y (Pimpl _ _ Px Hy))
    end.
End Acc_sidecond_generator.
(** We leave it opaque for now, as some simplification tactics
  might otherwise unfold the large Acc proof. Don't forget to make it transparent
  when computing. *)
Opaque Acc_intro_generator.

Section Reduce.

  Context {cf : checker_flags} {no : normalizing_flags}.

  Context (flags : RedFlags.t).

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Context {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.

(*  Local Definition gΣ := abstract_env_ext_rel Σ. *)

  Local Definition heΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf_ext Σ ∥ :=  abstract_env_ext_wf _ wfΣ.

  Local Definition hΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf Σ ∥ := abstract_env_ext_sq_wf _ _ _ wfΣ.

  Existing Instance Req_refl.

Lemma acc_dlexprod_gen P Q A B (leA : P -> A -> A -> Prop)
  (HQ : ∥ ∑ p , Q p ∥)
  (HP : forall p p' x x', Q p -> Q p' -> leA p x x' -> leA p' x x')
  (leB : forall x : A, B x -> B x -> Prop) :
  (forall x, well_founded (leB x)) ->
  forall x,
    Acc (fun t t' => forall (p:P), Q p -> leA p t t') x ->
    forall y,
      Acc (leB x) y ->
      Acc (fun t t' => forall (p:P), Q p -> @dlexprod A B (leA p) leB t t') (x;y).
Proof using Type.
intros hw. induction 1 as [x hx ih1].
intros y. induction 1 as [y hy ih2].
constructor.
intros [x' y'] h.
destruct HQ as [[p q]].
specialize (h p q).
simple inversion h.
- intro hA. inversion H0. inversion H1. subst.
  eapply ih1.
  + intros. now eapply (HP _ _ _ _ q).
  + apply hw.
- intro hB. rewrite <- H0.
  pose proof (projT2_eq H1) as p2.
  set (projT1_eq H1) as p1 in *; cbn in p1.
  destruct p1; cbn in p2; destruct p2.
  eapply ih2. assumption.
Qed.

Lemma dlexprod_Acc_gen P Q A B (leA : P -> A -> A -> Prop)
  (HQ : ∥ ∑ p , Q p ∥)
  (HP : forall p p' x x', Q p -> Q p' -> leA p x x' -> leA p' x x')
  (leB : forall x : A, B x -> B x -> Prop) :
    (forall x, well_founded (leB x)) ->
    forall x y,
      Acc (fun t t' => forall (p:P), Q p -> leA p t t') x ->
      Acc (fun t t' => forall (p:P), Q p -> @dlexprod A B (leA p) leB t t') (x;y).
Proof using Type.
  intros hB x y hA.
  eapply acc_dlexprod_gen ; try assumption.
  apply hB.
Qed.

Definition R_singleton Abs A
  (R : Abs -> A -> A -> Prop) (Q : Abs -> Prop) x (q : Q x)
  (HQ : forall x x' , Q x -> Q x' -> x = x') (a a' : A) :
  R x a a' <-> (forall x, Q x -> R x a a').
Proof using Type.
  split.
  - intros H x' q'.  specialize (HQ x x' q q'). subst; eauto.
  - eauto.
Defined.

Fixpoint Acc_equiv A (R R' : A -> A -> Prop)
  (Heq : forall a a', R a a' <-> R' a a') a
  (HAcc : Acc R a) : Acc R' a.
Proof using Type.
  econstructor. intros. apply Heq in H.
  destruct HAcc. eapply Acc_equiv; eauto.
Defined.

Corollary R_Acc_aux :
    forall Γ t p,
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t) ->
    (Acc (fun t t' => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R_aux Σ Γ t t') (t ; p)).
  Proof using normalization_in.
    intros Γ t p h.
    eapply dlexprod_Acc_gen.
    - apply abstract_env_ext_exists.
    - intros. eapply abstract_env_cored; try apply H1; eauto.
    - intros x. unfold well_founded.
      eapply posR_Acc.
    - destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
      destruct (heΣ _ wfΣ).
      eapply Acc_equiv; try
      eapply normalization_in; eauto.
      eapply R_singleton with (Q := abstract_env_ext_rel X)
          (R := fun Σ a a' => cored Σ Γ a a'); eauto.
      intros; eapply abstract_env_ext_irr; eauto.
  Defined.

  Corollary R_Acc :
    forall Γ t,
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zip t)) ->
      Acc (fun t t' => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ t t') t.
  Proof using normalization_in.
    intros Γ t h.
    pose proof (R_Acc_aux _ _ (stack_pos (fst t) (snd t)) h) as h'.
    clear h. rename h' into h.
    dependent induction h.
    constructor. intros y hy.
    eapply H0; eauto.
  Qed.



  Definition inspect {A} (x : A) : { y : A | y = x } := exist x eq_refl.

  Definition Pr (t' : term * stack) π :=
    snd (decompose_stack π) = snd (decompose_stack (snd t')).

  Abbreviation givePr := (_) (only parsing).

  Definition Pr' (t' : term * stack) :=
    isApp (fst t') = false /\
    (RedFlags.beta flags -> isLambda (fst t') -> isStackApp (snd t') = false).

  Abbreviation givePr' := (conj _ (fun β hl => _)) (only parsing).

  Abbreviation rec reduce t π :=
    (let smaller := _ in
     let '(exist res prf_Σ) := reduce t π smaller in
     exist res (fun Σ wfΣ => let '((conj prf (conj h (conj h1 h2)))) := prf_Σ Σ wfΣ in conj (Req_trans _ _ _ _ _ (R_to_Req _ (smaller Σ wfΣ))) (conj givePr givePr'))
    ) (only parsing).

  Abbreviation give t π :=
    (exist (t,π) (fun Σ wfΣ => conj _ (conj givePr givePr'))) (only parsing).

  Tactic Notation "zip" "fold" "in" hyp(h) :=
    lazymatch type of h with
    | context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C' in h
    end.

  Tactic Notation "zip" "fold" :=
    lazymatch goal with
    | |- context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C'
    end.

  Lemma Req_red Σ :
    forall Γ x y,
      Req Σ Γ y x ->
      ∥ red Σ Γ (zip x) (zip y) ∥.
  Proof using Type.
    intros Γ [t π] [t' π'] h; simpl.
    dependent destruction h.
    - repeat zip fold. rewrite H.
      constructor. reflexivity.
    - dependent destruction H.
      + eapply cored_red. assumption.
      + simpl in H0. inversion H0.
        constructor. reflexivity.
  Qed.


  (* Show Obligation Tactic. *)
  Ltac obTac :=
    (* program_simpl ; *)
    Program.Tactics.program_simplify ;
    Equations.CoreTactics.equations_simpl ;
    try Program.Tactics.program_solve_wf ;
    try reflexivity.

  Obligation Tactic := obTac.

  Equations discr_construct (t : term) : Prop :=
    discr_construct (tConstruct ind n ui) := False ;
    discr_construct _ := True.

  Inductive construct_view : term -> Type :=
  | view_construct : forall ind n ui, construct_view (tConstruct ind n ui)
  | view_other : forall t, discr_construct t -> construct_view t.

  Equations construct_viewc t : construct_view t :=
    construct_viewc (tConstruct ind n ui) := view_construct ind n ui ;
    construct_viewc t := view_other t I.

  (* Tailored view for _reduce_stack *)
  Equations red_discr (t : term) (π : stack) : Prop :=
    red_discr (tRel _) _ := False ;
    red_discr (tLetIn _ _ _ _) _ := False ;
    red_discr (tConst _ _) _ := False ;
    red_discr (tApp _ _) _ := False ;
    red_discr (tLambda _ _ _) (App_l _ :: _) := False ;
    red_discr (tFix _ _) _ := False ;
    red_discr (tCase _ _ _ _) _ := False ;
    red_discr (tProj _ _) _ := False ;
    red_discr _ _ := True.

  Inductive red_view : term -> stack -> Type :=
  | red_view_Rel c π : red_view (tRel c) π
  | red_view_LetIn A b B c π : red_view (tLetIn A b B c) π
  | red_view_Const c u π : red_view (tConst c u) π
  | red_view_App f a π : red_view (tApp f a) π
  | red_view_Lambda na A t a args : red_view (tLambda na A t) (App_l a :: args)
  | red_view_Fix mfix idx π : red_view (tFix mfix idx) π
  | red_view_Case ci p c brs π : red_view (tCase ci p c brs) π
  | red_view_Proj p c π : red_view (tProj p c) π
  | red_view_other t π : red_discr t π -> red_view t π.

  Equations red_viewc t π : red_view t π :=
    red_viewc (tRel c) π := red_view_Rel c π ;
    red_viewc (tLetIn A b B c) π := red_view_LetIn A b B c π ;
    red_viewc (tConst c u) π := red_view_Const c u π ;
    red_viewc (tApp f a) π := red_view_App f a π ;
    red_viewc (tLambda na A t) (App_l a :: args) := red_view_Lambda na A t a args ;
    red_viewc (tFix mfix idx) π := red_view_Fix mfix idx π ;
    red_viewc (tCase ci p c brs) π := red_view_Case ci p c brs π ;
    red_viewc (tProj p c) π := red_view_Proj p c π ;
    red_viewc t π := red_view_other t π I.

  Equations discr_construct_cofix (t : term) : Prop :=
    discr_construct_cofix (tConstruct ind n ui) := False ;
    discr_construct_cofix (tCoFix mfix idx) := False ;
    discr_construct_cofix _ := True.

  Inductive construct_cofix_view : term -> Type :=
  | ccview_construct : forall ind n ui, construct_cofix_view (tConstruct ind n ui)
  | ccview_cofix : forall mfix idx, construct_cofix_view (tCoFix mfix idx)
  | ccview_other : forall t, discr_construct_cofix t -> construct_cofix_view t.

  Equations cc_viewc t : construct_cofix_view t :=
    cc_viewc (tConstruct ind n ui) := ccview_construct ind n ui ;
    cc_viewc (tCoFix mfix idx) := ccview_cofix mfix idx ;
    cc_viewc t := ccview_other t I.

  Equations discr_construct0_cofix (t : term) : Prop :=
    discr_construct0_cofix (tConstruct ind n ui) := n <> 0 ;
    discr_construct0_cofix (tCoFix mfix idx) := False ;
    discr_construct0_cofix _ := True.

  Inductive construct0_cofix_view : term -> Type :=
  | cc0view_construct : forall ind ui, construct0_cofix_view (tConstruct ind 0 ui)
  | cc0view_cofix : forall mfix idx, construct0_cofix_view (tCoFix mfix idx)
  | cc0view_other : forall t, discr_construct0_cofix t -> construct0_cofix_view t.

  Equations cc0_viewc t : construct0_cofix_view t :=
    cc0_viewc (tConstruct ind 0 ui) := cc0view_construct ind ui ;
    cc0_viewc (tCoFix mfix idx) := cc0view_cofix mfix idx ;
    cc0_viewc t := cc0view_other t _.

  Equations _reduce_stack (Γ : context) (t : term) (π : stack)
            (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zip (t,π)))
            (reduce : forall t' π', (forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ (t',π') (t,π)) ->
                               { t'' : term * stack | forall Σ (wfΣ : abstract_env_ext_rel X Σ), Req Σ Γ t'' (t',π') /\ Pr t'' π' /\ Pr' t'' })
    : { t' : term * stack | forall Σ (wfΣ : abstract_env_ext_rel X Σ), Req Σ Γ t' (t,π) /\ Pr t' π /\ Pr' t' } :=

    _reduce_stack Γ t π h reduce with red_viewc t π := {

    | red_view_Rel c π with RedFlags.zeta flags := {
      | true with inspect (nth_error (Γ ,,, stack_context π) c) := {
        | @exist None eq := False_rect _ _ ;
        | @exist (Some d) eq with inspect d.(decl_body) := {
          | @exist None _ := give (tRel c) π ;
          | @exist (Some b) H := rec reduce (lift0 (S c) b) π
          }
        } ;
      | false := give (tRel c) π
      } ;

    | red_view_LetIn A b B c π with RedFlags.zeta flags := {
      | true := rec reduce (subst10 b c) π ;
      | false := give (tLetIn A b B c) π
      } ;

    | red_view_Const c u π with RedFlags.delta flags := {
      | true with inspect (abstract_env_lookup X c) := {
        | @exist (Some (ConstantDecl {| cst_body := Some body |})) eq :=
          let body' := subst_instance u body in
          rec reduce body' π ;
        | @exist (Some (InductiveDecl _)) eq := False_rect _ _ ;
        | @exist (Some _) eq := give (tConst c u) π ;
        | @exist None eq := False_rect _ _
        } ;
      | _ := give (tConst c u) π
      } ;

    | red_view_App f a π := rec reduce f (App_l a :: π) ;

    | red_view_Lambda na A t a args with inspect (RedFlags.beta flags) := {
      | @exist true eq1 := rec reduce (subst10 a t) args ;
      | @exist false eq1 := give (tLambda na A t) (App_l a :: args)
      } ;

    | red_view_Fix mfix idx π with RedFlags.fix_ flags := {
      | true with inspect (unfold_fix mfix idx) := {
        | @exist (Some (narg, fn)) eq1 with inspect (decompose_stack_at π narg) := {
          | @exist (Some (args, c, ρ)) eq2 with inspect (reduce c (Fix_app mfix idx args :: ρ) _) := {
            | @exist (@exist (t, ρ') prf) eq3 with construct_viewc t := {
              | view_construct ind n ui with inspect (decompose_stack ρ') := {
                | @exist (l, θ) eq4 :=
                  rec reduce fn (appstack args (App_l (mkApps (tConstruct ind n ui) l) :: ρ))
                } ;
              | view_other t ht with inspect (decompose_stack ρ') := {
                | @exist (l, θ) eq4 :=
                  give (tFix mfix idx) (appstack args (App_l (mkApps t l) :: ρ))
                }
              }
            } ;
          | _ := give (tFix mfix idx) π
          } ;
        | _ := give (tFix mfix idx) π
        } ;
      | false := give (tFix mfix idx) π
      } ;

    | red_view_Case ci p c brs π with RedFlags.iota flags := {
      | true with inspect (reduce c (Case_discr ci p brs :: π) _) := {
        | @exist (@exist (t,π') prf) eq with inspect (decompose_stack π') := {
          | @exist (args, ρ) prf' with cc_viewc t := {
            | ccview_construct ind' c' inst' with inspect (nth_error brs c') := {
              | exist (Some br) eqbr := rec reduce (iota_red ci.(ci_npar) p args br) π ;
              | exist None bot := False_rect _ _ } ;
            | ccview_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
              | @exist (Some (narg, fn)) eq' :=
                rec reduce (tCase ci p (mkApps fn args) brs) π ;
              | @exist None bot := False_rect _ _
              } ;
            | ccview_other t ht := give (tCase ci p (mkApps t args) brs) π
            }
          }
        } ;
      | false := give (tCase ci p c brs) π
      } ;

    | red_view_Proj p c π with RedFlags.iota flags := {
      | true with inspect (reduce c (Proj p :: π) _) := {
        | @exist (@exist (t,π') prf) eq with inspect (decompose_stack π') := {
          | @exist (args, ρ) prf' with cc0_viewc t := {
            | cc0view_construct ind' _
              with inspect (nth_error args (p.(proj_npars) + p.(proj_arg))) := {
              | @exist (Some arg) eqa := rec reduce arg π ;
              | @exist None eqa := False_rect _ _
              } ;
            | cc0view_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
              | @exist (Some (rarg, fn)) eq' :=
                rec reduce (tProj p (mkApps fn args)) π ;
              | @exist None bot := False_rect _ _
              } ;
            | cc0view_other t ht := give (tProj p (mkApps t args)) π
            }
          }
        } ;
      | false := give (tProj p c) π
      } ;

    | red_view_other t π discr := give t π

    }.

  (* tRel *)
  Next Obligation.
    left.
    econstructor.
    eapply red1_context.
    eapply red_rel. rewrite <- eq. cbn. f_equal.
    symmetry. assumption.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ].
    pose proof (welltyped_context _ hΣ _ _ (h _ wfΣ)) as hc.
    simpl in hc.
    (* Should be a lemma! *)
    clear - eq hc hΣ.
    revert c hc eq.
    generalize (Γ ,,, stack_context π) as Δ. clear Γ π.
    intro Γ.
    induction Γ ; intros c hc eq.
    - destruct hc as [A h].
      apply inversion_Rel in h as hh ; auto.
      destruct hh as [? [? [e ?]]].
      rewrite e in eq. discriminate eq.
    - destruct c.
      + cbn in eq. discriminate.
      + cbn in eq. eapply IHΓ ; try eassumption.
        destruct hc as [A h].
        apply inversion_Rel in h as hh ; auto.
        destruct hh as [? [? [e ?]]].
        cbn in e. rewrite e in eq. discriminate.
  Qed.

  (* tLetIn *)
  Next Obligation.
    left. econstructor.
    eapply red1_context.
    econstructor.
  Qed.

  (* tConst *)
  Next Obligation.
    left. econstructor. eapply red1_context.
    econstructor.
    - unfold declared_constant, declared_constant_gen.
      rewrite (abstract_env_lookup_correct _ _ _ wfΣ). rewrite <- eq. reflexivity.
    - cbn. reflexivity.
  Qed.

  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [wΣ].
    specialize (h _ wfΣ).
    eapply welltyped_context in h ; auto. simpl in h.
    destruct h as [T h].
    apply inversion_Const in h as [decl [? [d [? ?]]]] ; auto.
    unfold declared_constant, declared_constant_gen in d.
    rewrite (abstract_env_lookup_correct _ _ _ wfΣ), <- eq in d.
    discriminate.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [wΣ].
    specialize (h _ wfΣ).
    eapply welltyped_context in h ; auto. simpl in h.
    destruct h as [T h].
    apply inversion_Const in h as [decl [? [d [? ?]]]] ; auto.
    unfold declared_constant, declared_constant_gen in d.
    rewrite (abstract_env_lookup_correct _ _ _ wfΣ), <- eq in d.
    discriminate.
  Qed.

  (* tApp *)
  Next Obligation.
    right.
    simpl. unfold posR. simpl.
    rewrite stack_position_cons.
    eapply positionR_poscat_nonil. discriminate.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    unfold Pr in h. cbn in h.
    case_eq (decompose_stack π). intros l ρ e.
    cbn. rewrite e in h. cbn in h.
    assumption.
  Qed.

  (* tLambda *)
  Next Obligation.
    left. econstructor.
    cbn. eapply red1_context. econstructor.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    case_eq (decompose_stack args). intros l ρ e.
    cbn. unfold Pr in h. rewrite e in h. cbn in h.
    assumption.
  Qed.
  Next Obligation.
    rewrite β in eq1. discriminate.
  Qed.

  (* tFix *)
  Next Obligation.
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2). subst.
    eapply R_positionR.
    - cbn. rewrite zipc_appstack. cbn. reflexivity.
    - simpl. rewrite !stack_position_appstack, !stack_position_cons. simpl.
      rewrite <- app_assoc.
      eapply positionR_poscat.
      constructor.
  Qed.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. specialize (prf _ wfΣ). destruct prf as [r [p p0]].
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    pose proof (decompose_stack_at_length _ _ _ _ _ eq2).
    case_eq (decompose_stack ρ). intros l' θ' e'.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite H in e. rewrite decompose_stack_appstack in e.
    cbn in e. rewrite e' in e. cbn in e. inversion e. subst. clear e.

    case_eq (decompose_stack ρ'). intros ll s e1.
    pose proof (decompose_stack_eq _ _ _ e1). subst.

    eapply R_Req_R.
    - instantiate (1 := (tFix mfix idx, appstack (args ++ (mkApps (tConstruct ind n ui) l) :: l') π')).
      left. cbn. rewrite 2!zipc_appstack. cbn. rewrite zipc_appstack.
      repeat zip fold. eapply cored_context.
      assert (forall args l u v, mkApps (tApp (mkApps u args) v) l = mkApps u (args ++ v :: l)) as thm.
      { clear. intro args. induction args ; intros l u v.
        - reflexivity.
        - cbn. rewrite IHargs. reflexivity.
      }
      rewrite thm.
      left. eapply red_fix.
      + eauto.
      + unfold is_constructor.
        rewrite nth_error_app2 by eauto.
        replace (#|args| - #|args|) with 0 by auto with arith.
        cbn.
        unfold isConstruct_app.
        rewrite decompose_app_mkApps by reflexivity.
        reflexivity.
    - destruct r.
      + inversion H0. subst.
        destruct ll.
        * cbn in H3. subst. cbn in eq4. inversion eq4. subst.
          reflexivity.
        * cbn in H3. discriminate H3.
      + dependent destruction H0.
        * cbn in H0. rewrite 2!zipc_appstack in H0.
          rewrite decompose_stack_appstack in eq4.
          case_eq (decompose_stack s). intros l0 s0 e2.
          rewrite e2 in eq4. cbn in eq4.
          destruct l0.
          -- rewrite app_nil_r in eq4. inversion eq4. subst. clear eq4.
             pose proof (decompose_stack_eq _ _ _ e2) as ee. cbn in ee.
             symmetry in ee. subst.
             right. left.
             cbn. rewrite !zipc_appstack.
             unfold Pr in p. cbn in p.
             rewrite e1 in p. cbn in p. subst.
             cbn in H0.
             clear - H0.

             match goal with
             | |- ?A =>
               let e := fresh "e" in
               let B := type of H0 in
               assert (A = B) as e ; [| rewrite e ; assumption ]
             end.
             set (t := tConstruct ind n ui). clearbody t.
             set (f := tFix mfix idx). clearbody f.
             f_equal.
             ++ clear. revert ll π' l' t f.
                induction args ; intros ll π' l' t f.
                ** cbn. rewrite zipc_appstack. reflexivity.
                ** cbn. rewrite IHargs. reflexivity.
             ++ clear. revert π' l' c f.
                induction args ; intros π' l' c f.
                ** cbn. reflexivity.
                ** cbn. rewrite IHargs. reflexivity.
          -- pose proof (decompose_stack_eq _ _ _ e2) as ee. cbn in ee.
             subst. exfalso.
             eapply decompose_stack_not_app. eassumption.
        * cbn in H1. inversion H1.
          rewrite 2!zipc_appstack in H3.
          unfold Pr in p. cbn in p.
          rewrite e1 in p. cbn in p. subst.
          cbn in H3. rewrite zipc_appstack in H3.
          apply zipc_inj in H3.
          apply PCUICAstUtils.mkApps_inj in H3.
          inversion H3. subst.
          rewrite e1 in eq4. inversion eq4. subst.
          reflexivity.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    unfold Pr in h. cbn in h.
    rewrite decompose_stack_appstack in h. cbn in h.
    case_eq (decompose_stack ρ). intros l1 ρ1 e.
    rewrite e in h. cbn in h. subst.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    subst.
    rewrite decompose_stack_appstack. cbn.
    rewrite e. cbn. reflexivity.
  Qed.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. specialize (prf _ wfΣ). destruct prf as [r [p p0]].
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2) as e2.
    pose proof (decompose_stack_at_length _ _ _ _ _ eq2).
    case_eq (decompose_stack ρ). intros l' θ' e'.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite e2 in e. rewrite decompose_stack_appstack in e.
    cbn in e. rewrite e' in e. cbn in e. inversion e. subst. clear e.
    symmetry in eq4. apply decompose_stack_eq in eq4 as ?. subst.

    rewrite e2.
    destruct r as [r | r].
    - inversion r. subst.
      destruct l. 2: discriminate.
      cbn in *. subst.
      left. reflexivity.
    - unfold Pr in p. cbn in p.
      rewrite eq4 in p. simpl in p. subst.
      dependent destruction r.
      + cbn in H. rewrite zipc_appstack in H.
        cbn in H. rewrite !zipc_appstack in H.
        right. left. cbn. rewrite !zipc_appstack. cbn.
        rewrite !zipc_appstack. assumption.
      + cbn in H0. inversion H0.
        rewrite !zipc_appstack in H2. cbn in H2.
        rewrite zipc_appstack in H2.
        apply zipc_inj in H2. apply PCUICAstUtils.mkApps_inj in H2.
        inversion H2. subst.
        left. reflexivity.
  Qed.
  Next Obligation.
    symmetry in eq4.
    clear eq3. specialize (prf _ wfΣ). destruct prf as [r [p p0]].
    unfold Pr in p. cbn in p.
    rewrite eq4 in p. simpl in p. subst.
    unfold Pr. cbn.
    rewrite decompose_stack_appstack. cbn.
    case_eq (decompose_stack π). intros ll π' e. cbn.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2) as e2.
    pose proof (decompose_stack_at_length _ _ _ _ _ eq2).
    case_eq (decompose_stack ρ). intros l' θ' e'. cbn.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite e2 in e. rewrite decompose_stack_appstack in e.
    cbn in e. rewrite e' in e. cbn in e. inversion e. reflexivity.
  Qed.

  (* tCase *)
  Next Obligation.
    right. unfold posR. simpl.
    rewrite stack_position_cons.
    eapply positionR_poscat_nonil. discriminate.
  Qed.
  Next Obligation.
    clear eq.
    pose proof (hΣ := hΣ _ wfΣ).
    sq. specialize (prf _ wfΣ). destruct prf as [r [p0 p1]].

    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    apply eq_sym, decompose_stack_eq in prf'; subst.
    apply Req_red in r; cbn in r.
    sq.
    rewrite zipc_appstack in r.
    cbn in r.
    pose proof r as r'. specialize (h _ wfΣ).
    eapply red_welltyped in r' ; tea.
    zip fold in r'.
    apply welltyped_context in r' as (?&typ); auto; cbn in *.
    apply PCUICInductiveInversion.invert_Case_Construct in typ as H; auto.
    2: now sq.
    destruct H as (?&?&nth&?); subst.
    rewrite nth in eqbr; noconf eqbr.
    constructor.
    eapply cored_red_cored; cycle 1.
    - zip fold in r; exact r.
    - constructor.
      eapply red1_context.
      eapply red_iota; eauto.
  Qed.
  Next Obligation.
    clear eq.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [p0 p1]].
    sq.
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    apply eq_sym, decompose_stack_eq in prf'; subst.
    apply Req_red in r; cbn in r.
    sq.
    rewrite zipc_appstack in r.
    cbn in r.
    pose proof r as r'.
    eapply red_welltyped in r; eauto.
    zip fold in r.
    apply welltyped_context in r as (?&typ); auto; cbn in *.
    apply PCUICInductiveInversion.invert_Case_Construct in typ as H; auto.
    2: now sq.
    destruct H as (?&?&nth&?); subst.
    rewrite nth in bot; congruence.
  Qed.
  Next Obligation.
    clear eq.
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [p0 p1]].
    sq.
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    apply eq_sym, decompose_stack_eq in prf'; subst.
    apply Req_red in r; cbn in r. pose hΣ.
    sq.
    rewrite zipc_appstack in r.
    cbn in r.
    pose proof r as r'.
    eapply red_welltyped in r; eauto.
    zip fold in r.
    apply welltyped_context in r as (?&typ); auto; cbn in *.
    constructor.
    eapply cored_red_cored; cycle 1.
    - zip fold in r'; exact r'.
    - constructor.
      eapply red1_context.
      eapply red_cofix_case; eauto.
  Qed.
  Next Obligation.
    clear eq. destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [p0 p1]].
    sq.
    sq.
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    apply eq_sym, decompose_stack_eq in prf'; subst.
    apply Req_red in r; cbn in r.
    sq.
    pose proof r as r'.
    eapply red_welltyped in r; eauto.
    zip fold in r.
    apply welltyped_context in r as (?&typ); auto; cbn in *.
    apply inversion_CoFix in typ as (?&?&?&?&?&?&?); auto.
    unfold unfold_cofix in bot.
    rewrite e in bot.
    congruence.
  Qed.
  Next Obligation.
    clear eq reduce h.
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [p0 p1]].
    destruct r.
    - inversion H. subst.
      clear H.
      cbn in prf'. inversion prf'. subst. reflexivity.
    - unfold Pr in p0. cbn in p0.
      rewrite <- prf' in p0. cbn in p0. subst.
      dependent destruction H.
      + cbn in H. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H. cbn in H.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H2. cbn in H2.
        apply zipc_inj in H2. inversion H2. subst.
        reflexivity.
  Qed.

  (* tProj *)
  Next Obligation.
    right. unfold posR. simpl.
    rewrite stack_position_cons.
    rewrite <- app_nil_r.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    pose proof (hΣ := hΣ _ wfΣ).
    destruct (prf Σ wfΣ)  as [r [p' p0]].
    sq.
    left.
    apply Req_red in r as hr.
    sq.
    pose proof (red_welltyped _ hΣ (h _ wfΣ) hr) as hh.
    eapply cored_red_cored ; try eassumption.
    unfold Pr in p'. simpl in p'. pose proof p' as p''.
    rewrite <- prf' in p''. simpl in p''. subst.
    symmetry in prf'. apply decompose_stack_eq in prf' as ?.
    subst. cbn. rewrite zipc_appstack. cbn.
    do 2 zip fold. eapply cored_context.
    constructor.
    cbn in hh. rewrite zipc_appstack in hh. cbn in hh.
    zip fold in hh. apply welltyped_context in hh. 2: assumption.
    simpl in hh. apply Proj_Construct_ind_eq in hh. all: eauto.
    subst. constructor. eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [pr p0]].
    sq.
    unfold Pr in pr. simpl in pr.
    pose proof pr as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    symmetry in prf'. apply decompose_stack_eq in prf' as ?.
    subst.
    apply Req_red in r as hr.
    sq.
    pose proof (red_welltyped _ hΣ (h _ wfΣ) hr) as hh.
    cbn in hh. rewrite zipc_appstack in hh. cbn in hh.
    zip fold in hh.
    apply welltyped_context in hh. 2: assumption.
    simpl in hh.
    apply Proj_red_cond in hh. all: eauto.
  Qed.
  Next Obligation.
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [pr p0]].
    unfold Pr in pr. simpl in pr.
    pose proof pr as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    dependent destruction r.
    - inversion H. subst.
      left. eapply cored_context.
      constructor.
      simpl in prf'. inversion prf'. subst.
      eapply red_cofix_proj with (args := []). eauto.
    - clear eq.
      dependent destruction H.
      + left.
        symmetry in prf'. apply decompose_stack_eq in prf' as ?. subst.
        cbn in H. rewrite zipc_appstack in H. cbn in H.
        eapply cored_trans' ; try eassumption.
        zip fold. eapply cored_context.
        constructor. eapply red_cofix_proj. eauto.
      + left.
        cbn in H0. destruct y'. inversion H0. subst. clear H0.
        symmetry in prf'. apply decompose_stack_eq in prf' as ?. subst.
        rewrite zipc_appstack in H2. cbn in H2.
        cbn. rewrite H2.
        zip fold. eapply cored_context.
        constructor. eapply red_cofix_proj. eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [pr p0]].
    sq.
    unfold Pr in pr. simpl in pr.
    pose proof pr as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    assert (h' : welltyped Σ Γ (zip (tProj p (mkApps (tCoFix mfix idx) args), π))).
    { dependent destruction r.
      - inversion H. subst.
        simpl in prf'. inversion prf'. subst. now apply h.
      - clear eq. dependent destruction H.
        + apply cored_red in H. destruct H as [r].
          eapply red_welltyped ; eauto.
          symmetry in prf'. apply decompose_stack_eq in prf'. subst.
          cbn in r. rewrite zipc_appstack in r. cbn in r.
          assumption.
        + cbn in H0. destruct y'. inversion H0. subst. clear H0.
          symmetry in prf'. apply decompose_stack_eq in prf'. subst.
          rewrite zipc_appstack in H2. cbn in H2.
          cbn. rewrite <- H2. now apply h.
          }
    replace (zip (tProj p (mkApps (tCoFix mfix idx) args), π))
      with (zip (tCoFix mfix idx, appstack args (Proj p :: π)))
      in h'.
    - sq.
      apply welltyped_context in h' ; auto. simpl in h'.
      destruct h' as [T h'].
      apply inversion_CoFix in h' ; auto.
      destruct h' as [decl [? [e [? [? ?]]]]].
      unfold unfold_cofix in bot.
      rewrite e in bot. discriminate.
    - cbn. rewrite zipc_appstack. reflexivity.
  Qed.
  Next Obligation.
    clear eq.
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [pr p0]].
    dependent destruction r.
    - inversion H. subst. cbn in prf'. inversion prf'. subst.
      cbn. reflexivity.
    - unfold Pr in pr. cbn in pr.
      rewrite <- prf' in pr. cbn in pr. subst.
      dependent destruction H.
      + cbn in H. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H. cbn in H.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H2. cbn in H2.
        apply zipc_inj in H2. inversion H2. subst.
        reflexivity.
  Qed.

  (* Other *)
  Next Obligation.
    revert discr.
    apply_funelim (red_discr t π). all: auto.
  Qed.
  Next Obligation.
    revert discr hl.
    apply_funelim (red_discr t π). all: easy.
  Qed.

  Lemma welltyped_R_pres Σ (wfΣ : abstract_env_ext_rel X Σ) Γ :
    forall x y : term × stack, welltyped Σ Γ (zip x) -> R Σ Γ y x -> welltyped Σ Γ (zip y).
  Proof using Type.
    intros x y H HR.
    pose proof (heΣ := heΣ _ wfΣ).
    pose proof (hΣ := hΣ _ wfΣ).
    clear wfΣ X_type X normalization_in.
    sq.
    destruct x as [x πx], y as [y πy].
    dependent induction HR.
    - eapply cored_welltyped. all: eauto.
    - simpl in H1. revert H1; intros [= H2 _].
      now rewrite <- H2.
  Qed.

  Section reducewf.
    Context (Γ : context).

    Abbreviation sigmaarg :=
      (sigma (fun t => sigma (fun π => forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ Γ (zipc t π)))).

    Local Instance wf_proof : WellFounded (fun x y : sigmaarg =>
        forall Σ, abstract_env_ext_rel X Σ -> R Σ Γ (pr1 x, pr1 (pr2 x)) (pr1 y, pr1 (pr2 y))).
    Proof using normalization_in.
      intros [t [π wt]].
      (* We fuel the accessibility proof to run reduction inside Rocq. *)
      unshelve eapply (Acc_intro_generator
        (R:=fun x y : sigmaarg => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ (x.(pr1), x.(pr2).(pr1)) (y.(pr1), y.(pr2).(pr1)))
        (P:=fun x : sigmaarg => forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zip (x.(pr1), x.(pr2).(pr1))))
        (fun x y Px Hy => _) 1000 _ {| pr1 := t; pr2 := {| pr1 := π; pr2 := wt |} |} wt).
      - cbn in *. intros. destruct y as [t' [π' wt']]. cbn. now apply wt'.
      - cbn in *. intros.
        destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
        destruct (hΣ _ wfΣ) as [hΣ]. pose proof (R_Acc Γ (t0.(pr1), t0.(pr2).(pr1)) H).
        clear -H0. destruct t0 as [t [π wt]].
        cbn in *. revert wt.
        depind H0. intros wt. constructor. intros. eapply H0.
        * cbn in H1. exact H1.
        * reflexivity.
  Defined.

  Equations reduce_stack_full (t : term) (π : stack) (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zip (t,π))) :
    { t' : term * stack | forall Σ (wfΣ : abstract_env_ext_rel X Σ), Req Σ Γ t' (t, π) /\ Pr t' π /\ Pr' t' }
    by wf (t, π) (fun (x y : term * stack) => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ x y) :=
    reduce_stack_full t π h := _reduce_stack Γ t π h (fun t' π' hr => reduce_stack_full t' π' (fun Σ wfΣ' => welltyped_R_pres Σ wfΣ' Γ _ _ (h Σ wfΣ') (hr Σ wfΣ'))).

  End reducewf.

  Definition reduce_stack Γ t π h :=
    let '(exist ts _) := reduce_stack_full Γ t π h in ts.

  Lemma reduce_stack_Req :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h,
     Req Σ Γ (reduce_stack Γ t π h) (t, π).
  Proof using Type.
    intros Σ wfΣ Γ t π h.
    unfold reduce_stack.
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r _]];
    eassumption.
  Qed.

  Theorem reduce_stack_sound :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h,
      ∥ Σ ;;; Γ ⊢ zip (t, π) ⇝ zip (reduce_stack Γ t π h) ∥.
  Proof using Type.
    intros Σ wfΣ Γ t π h.
    assert (req := reduce_stack_Req Σ wfΣ _ _ _ h).
    eapply Req_red in req.
    destruct (hΣ _ wfΣ).
    sq. eapply into_closed_red; fvs.
  Qed.

  Lemma reduce_stack_decompose :
    forall Γ t π h,
      snd (decompose_stack (snd (reduce_stack Γ t π h))) =
      snd (decompose_stack π).
  Proof using Type.
    intros Γ t π h.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    unfold reduce_stack.
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p p']]];
    try eassumption.
    unfold Pr in p. symmetry. assumption.
  Qed.

  Lemma reduce_stack_context :
    forall Γ t π h,
      stack_context (snd (reduce_stack Γ t π h)) =
      stack_context π.
  Proof using Type.
    intros Γ t π h.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (reduce_stack_decompose Γ t π h) as hd.
    case_eq (decompose_stack π). intros l ρ e1.
    case_eq (decompose_stack (snd (reduce_stack Γ t π h))). intros l' ρ' e2.
    rewrite e1 in hd. rewrite e2 in hd. cbn in hd. subst.
    pose proof (decompose_stack_eq _ _ _ e1).
    pose proof (decompose_stack_eq _ _ _ e2) as eq.
    rewrite eq. subst.
    rewrite 2!stack_context_appstack. reflexivity.
  Qed.

  Definition isred (t : term * stack) :=
    isApp (fst t) = false /\
    (isLambda (fst t) -> isStackApp (snd t) = false).

  Lemma reduce_stack_isred :
    forall Γ t π h,
      RedFlags.beta flags ->
      isred (reduce_stack Γ t π h).
  Proof using Type.
    intros Γ t π h hr.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    unfold reduce_stack.
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]]; eauto.
    split.
    - assumption.
    - apply hLam. assumption.
  Qed.

  Lemma reduce_stack_noApp :
    forall Γ t π h,
      isApp (fst (reduce_stack Γ t π h)) = false.
  Proof using Type.
    intros Γ t π h.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    unfold reduce_stack.
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]]; eauto.
  Qed.

  Lemma reduce_stack_noLamApp :
    forall Γ t π h,
      RedFlags.beta flags ->
      isLambda (fst (reduce_stack Γ t π h)) ->
      isStackApp (snd (reduce_stack Γ t π h)) = false.
  Proof using Type.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]]; eauto.
  Qed.

  Definition reduce_term Γ t
    (h : forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) :=
    zip (reduce_stack Γ t [] h).

  Theorem reduce_term_sound :
    forall Γ t (h : forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
      Σ, abstract_env_ext_rel X Σ ->
      ∥ Σ ;;; Γ ⊢ t ⇝ reduce_term Γ t h ∥.
  Proof using Type.
    intros Γ t h Σ wfΣ.
    unfold reduce_term.
    refine (reduce_stack_sound _ _ _ _ [] _); eauto.
  Qed.

  Scheme Acc_ind' := Induction for Acc Sort Prop.

  Lemma Fix_F_prop :
    forall A R P f (pred : forall x : A, P x -> Prop) x hx,
      (forall x aux, (forall y hy, pred y (aux y hy)) -> pred x (f x aux)) ->
      pred x (@Fix_F A R P f x hx).
  Proof using Type.
    intros A R P f pred x hx h.
    induction hx using Acc_ind'.
    cbn. eapply h. assumption.
  Qed.

  Lemma reduce_stack_prop :
    forall Γ t π h (P : term × stack -> term × stack -> Prop),
      (forall t π h aux,
          (forall t' π' hR, P (t', π') (` (aux t' π' hR))) ->
          P (t, π) (` (_reduce_stack Γ t π h aux))) ->
      P (t, π) (reduce_stack Γ t π h).
  Proof using Type.
    intros Γ t π h P hP.
    unfold reduce_stack.
    case_eq (reduce_stack_full Γ t π h).
    apply_funelim (reduce_stack_full Γ t π h); clear -hP.
    intros t π wt ih [t' ρ] ? e.
    match type of e with
    | _ = ?u =>
      change (P (t, π) (` u))
    end.
    rewrite <- e.
    apply hP. intros t'0 π' hR.
    specialize (ih _ _ hR).
    set (r := reduce_stack_full _ _ _ _) in *.
    eapply (ih _ (proj2_sig r)). clearbody r. now destruct r.
  Qed.

  Lemma decompose_stack_at_appstack_None l s n :
    isStackApp s = false ->
    nth_error l n = None <->
    decompose_stack_at (appstack l s) n = None.
  Proof using Type.
    intros no_app.
    induction l in l, n |- *; cbn in *.
    - rewrite nth_error_nil.
      split; intros; try easy.
      destruct s as [|[]]; cbn in *; easy.
    - destruct n; [easy|].
      cbn in *.
      split.
      + rewrite IHl.
        now intros ->.
      + rewrite IHl.
        now destruct decompose_stack_at as [((?&?)&?)|]; intros.
  Qed.

  Lemma mkApps_tApp hd arg args :
    mkApps (tApp hd arg) args = mkApps hd (arg :: args).
  Proof using Type. reflexivity. Qed.

  Lemma tApp_mkApps hd args arg :
    tApp (mkApps hd args) arg = mkApps hd (args ++ [arg]).
  Proof using Type.
    change (tApp ?hd ?a) with (mkApps hd [a]).
    now rewrite mkApps_app.
  Qed.

  Lemma whnf_non_ctor_finite_ind_typed Σ Γ t ind u args :
    wf Σ ->
    whnf flags Σ Γ t ->
    isConstruct_app t = false ->
    check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite = false ->
    Σ ;;; Γ |- t : mkApps (tInd ind u) args ->
    whne flags Σ Γ t.
  Proof using Type.
    intros wf wh ctor fin typ.
    destruct wh.
    - easy.
    - apply inversion_Sort in typ as (?&?&?); auto.
      exfalso; eapply invert_cumul_sort_ind; eauto.
    - apply inversion_Prod in typ as (?&?&?&?&?); auto.
      exfalso; eapply invert_cumul_sort_ind; eauto.
    - apply inversion_Lambda in typ as (?&?&?&?); auto.
      exfalso; eapply invert_cumul_prod_ind; eauto.
    - unfold isConstruct_app in ctor.
      now rewrite decompose_app_mkApps in ctor.
    - exfalso; eapply invert_ind_ind; eauto.
    - exfalso; eapply invert_fix_ind; eauto.
      unfold unfold_fix. destruct o as [[? [-> ?]] | ->]; eauto.
    - apply typing_cofix_coind in typ; auto.
      unfold is_true in typ.
      unfold PCUICAst.PCUICEnvironment.fst_ctx in *.
      congruence.
    - eapply inversion_Prim in typ as (prim_ty & cdecl & [? ? ? ?]); tea.
      now eapply (invert_cumul_prim_type_ind) in w; tea.
  Qed.

  Definition isCoFix_app t :=
    match (decompose_app t).1 with
    | tCoFix _ _ => true
    | _ => false
    end.

  Lemma whnf_non_ctor_non_cofix_ind_typed Σ Γ t ind u args :
    wf Σ ->
    whnf flags Σ Γ t ->
    isConstruct_app t = false ->
    isCoFix_app t = false ->
    Σ ;;; Γ |- t : mkApps (tInd ind u) args ->
    whne flags Σ Γ t.
  Proof using Type.
    intros wf wh ctor cof typ.
    destruct wh.
    - easy.
    - apply inversion_Sort in typ as (?&?&?); auto.
      exfalso; eapply invert_cumul_sort_ind; eauto.
    - apply inversion_Prod in typ as (?&?&?&?&?); auto.
      exfalso; eapply invert_cumul_sort_ind; eauto.
    - apply inversion_Lambda in typ as (?&?&?&?); auto.
      exfalso; eapply invert_cumul_prod_ind; eauto.
    - unfold isConstruct_app in ctor.
      now rewrite decompose_app_mkApps in ctor.
    - exfalso; eapply invert_ind_ind; eauto.
    - exfalso; eapply invert_fix_ind; eauto.
      unfold unfold_fix. destruct o as [[? [-> ?]] | ->]; eauto.
    - unfold isCoFix_app in cof.
      now rewrite decompose_app_mkApps in cof.
    - eapply inversion_Prim in typ as [prim_ty [cdecl [? ? ? ?]]]; tea.
      now eapply invert_cumul_prim_type_ind in w; tea.
  Qed.

  Lemma whnf_fix_arg_whne mfix idx body Σ Γ t before args aftr ty :
    wf Σ ->
    unfold_fix mfix idx = Some (#|before|, body) ->
    match t with
    | tConstruct _ _ _ => False
    | tApp _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps t args) ->
    Σ ;;; Γ |- mkApps (tFix mfix idx) (before ++ mkApps t args :: aftr) : ty ->
    whne flags Σ Γ (mkApps t args).
  Proof using Type.
    intros wf uf shape wh typ.
    apply inversion_mkApps in typ as (fix_ty & typ_fix & typ_args); auto.
    apply inversion_Fix in typ_fix as (def&?&?&?&?&?&?); auto.
    eapply All_nth_error in a; eauto.
    apply isTypeRel_isType in a.
    eapply wf_fixpoint_spine in i; eauto.
    2: { eapply PCUICSpine.typing_spine_strengthen; eauto. }
    unfold unfold_fix in uf.
    rewrite e in uf.
    rewrite nth_error_snoc in i by congruence.
    destruct i as (?&?&?&typ&fin).
    eapply whnf_non_ctor_finite_ind_typed; try eassumption.
    - unfold isConstruct_app.
      rewrite decompose_app_mkApps by (now destruct t).
      cbn.
      now destruct t.
    - destruct check_recursivity_kind eqn:cofin in |- *; [|easy].
      eapply check_recursivity_kind_inj in fin; [|exact cofin].
      congruence.
  Qed.

  Lemma whnf_case_arg_whne Σ Γ hd args ci p brs T :
    wf Σ ->
    match hd with
    | tApp _ _
    | tConstruct _ _ _
    | tCoFix _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    Σ;;; Γ |- tCase ci p (mkApps hd args) brs : T ->
    whne flags Σ Γ (mkApps hd args).
  Proof using Type.
    intros wf shape wh typ.
    apply inversion_Case in typ as (?&?&isdecl&?&[]&?); auto.
    eapply whnf_non_ctor_finite_ind_typed; try eassumption.
    - unfold isConstruct_app.
      now rewrite decompose_app_mkApps; destruct hd.
    - unfold isCoFinite in not_cofinite.
      unfold check_recursivity_kind.
      cbn.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      unfold declared_inductive, declared_minductive in isdecl.
      cbn in isdecl.
      rewrite (proj1 isdecl).
      now destruct ind_finite.
  Qed.

  Lemma whnf_proj_arg_whne Σ Γ hd args p T :
    wf Σ ->
    match hd with
    | tApp _ _
    | tCoFix _ _ => False
    | tConstruct _ c _ => c <> 0
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    Σ ;;; Γ |- tProj p (mkApps hd args) : T ->
    whne flags Σ Γ (mkApps hd args).
  Proof using Type.
    intros wf shape wh typ.
    assert (typ' := typ).
    apply inversion_Proj in typ as (?&?&?&?&?&?&?&?&?); auto.
    cbn in *.
    eapply whnf_non_ctor_non_cofix_ind_typed; try eassumption.
    - unfold isConstruct_app.
      rewrite decompose_app_mkApps by (now destruct hd).
      cbn.
      destruct hd; try easy.
      destruct p as [].
      eapply PCUICInductiveInversion.invert_Proj_Construct in typ' as (?&?&?); auto.
      2: sq; eapply wf.
      congruence.
    - unfold isCoFix_app.
      now rewrite decompose_app_mkApps; destruct hd.
  Qed.

  Lemma reduce_stack_whnf :
    forall Γ t π h Σ (wfΣ : abstract_env_ext_rel X Σ),
      let '(u, ρ) := reduce_stack Γ t π h in
       ∥whnf flags Σ (Γ ,,, stack_context ρ) (zipp u ρ)∥.
  Proof using Type.
    intros Γ t π h Σ wfΣ.
    eapply reduce_stack_prop
      with (P := fun x y =>
        let '(u, ρ) := y in
        ∥whnf flags Σ (Γ ,,, stack_context ρ) (zipp u ρ)∥
      ).
    clear -wfΣ.
    intros t π h aux.
    apply_funelim (_reduce_stack Γ t π h aux); clear -wfΣ.
    all: simpl.
    all: intros *.
    all: repeat match goal with
      [ |- (forall (t' : term) (π' : stack)
         (hR : forall Σ,
               abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ }) -> _ ] => intros reduce
    | [ |- (forall (t' : term) (π' : stack)
        (hR : forall Σ,
          abstract_env_ext_rel X Σ -> R Σ _ _ _), _) -> _ ] => intros haux
          | [ |- _ ] => intros ?
    end.
    all: try match goal with
             | |- context[False_rect _ ?f] => destruct f
             end.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] H eq.
      rewrite eq in haux. cbn in haux.
      assumption.
    - clear Heq.
      revert discr.
      revert h reduce haux; apply_funelim (red_discr t π); clear -wfΣ.
      all: intros; try destruct discr.
      all: try solve [ constructor ; constructor ].
      all: try solve [
        unfold zipp ; case_eq (decompose_stack π) ; intros ;
        do 2 constructor ; eapply whne_mkApps ; constructor
      ].
      + unfold zipp.
        case_eq (decompose_stack π). intros l ρ e.
        apply decompose_stack_eq in e. subst.
        destruct l.
        * simpl. eauto with pcuic.
        * exfalso.
          destruct (hΣ _ wfΣ) as [hΣ].
          cbn in h. zip fold in h.
          specialize (h _ wfΣ).
          apply welltyped_context in h; auto.
          simpl in h. rewrite stack_context_appstack in h.
          destruct h as [T h].
          apply inversion_App in h as (?&?&?&?&?); auto.
          apply inversion_Sort in t0 as (?&?&?); auto.
          eapply PCUICConversion.ws_cumul_pb_Sort_Prod_inv; eauto.
      + unfold zipp.
        case_eq (decompose_stack π). intros l ρ e.
        apply decompose_stack_eq in e. subst.
        destruct l.
        * simpl. eauto with pcuic.
        * exfalso.
          destruct (hΣ _ wfΣ) as [hΣ].
          cbn in h. zip fold in h.
          specialize (h _ wfΣ). apply welltyped_context in h; auto.
          simpl in h. rewrite stack_context_appstack in h.
          destruct h as [T h].
          apply inversion_App in h as (?&?&?&?&?); auto.
          apply inversion_Prod in t0 as (?&?&?&?&?); auto.
          eapply PCUICConversion.ws_cumul_pb_Sort_Prod_inv; eauto.
        + unfold zipp.
          case_eq (decompose_stack π). intros l ρ e.
          apply decompose_stack_eq in e. subst.
          destruct l.
          * simpl. eauto with pcuic.
          * exfalso.
            destruct (hΣ _ wfΣ) as [hΣ].
            cbn in h. zip fold in h.
            specialize (h _ wfΣ).
            apply welltyped_context in h; auto.
            simpl in h. rewrite stack_context_appstack in h.
            destruct h as [T h].
            apply inversion_App in h as (?&?&?&?&?); auto.
            apply inversion_Prim in t0 as (prim_ty & cdecl & [? ? ? ?]); auto.
            eapply PCUICConversion.invert_cumul_prim_type_prod; eauto.
    - unfold zipp. case_eq (decompose_stack π). intros l ρ e.
      constructor. constructor. eapply whne_mkApps.
      eapply whne_rel_nozeta. assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] Ha eq'. cbn.
      rewrite eq' in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. econstructor.
      rewrite <- eq. cbn.
      cbn in H. inversion e. reflexivity.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] Ha eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. eapply whne_letin_nozeta. assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. eapply whne_const_nodelta. assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] Ha eq'. cbn.
      rewrite eq' in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. econstructor.
      + symmetry. erewrite abstract_env_lookup_correct'; eauto.
      + reflexivity.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] Ha eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - unfold zipp. destruct decompose_stack eqn:eq.
      apply decompose_stack_noStackApp in eq as ?.
      apply decompose_stack_eq in eq.
      destruct l.
      + cbn in *; subst.
        cbn in *; congruence.
      + cbn.
        constructor.
        apply whnf_mkApps.
        apply whne_app.
        now apply whne_lam_nobeta.
    - unfold zipp.
      destruct decompose_stack.
      constructor.
      apply whnf_mkApps.
      now apply whne_fix_nofix.
    - unfold zipp.
      destruct decompose_stack.
      constructor.
      apply whnf_fixapp.
      clear -e. unfold unfold_fix in e. now destruct nth_error.
    - unfold zipp.
      destruct decompose_stack eqn:eq.
      apply decompose_stack_noStackApp in eq as ?.
      apply decompose_stack_eq in eq.
      subst.
      constructor.
      apply whnf_fixapp.
      clear -e eq1 H. unfold unfold_fix in eq1. symmetry in e.
      apply <- decompose_stack_at_appstack_None in e ; eauto.
      destruct (nth_error mfix idx) ; [left | now right]. eexists; split ; now eauto.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        specialize (haux x y z) as ?;
        destruct (reduce x y z)
      end.
      destruct (a _ wfΣ) as (?&?&?&?).
      now destruct x.
    - match type of eq3 with
      | context [ reduce ?x ?y ?z ] =>
        specialize (haux x y z);
          destruct (reduce x y z)
      end.
      noconf eq3; cbn in *.
      pose proof (hΣ _ wfΣ) as [hΣ].
      clear -wfΣ hΣ eq4 ht eq2 eq1 h prf haux.
      destruct (prf _ wfΣ) as (r&stacks&?).
      unfold Pr in stacks.
      cbn in *.
      unfold snd in stacks.
      rewrite <- eq4 in stacks.
      subst.
      symmetry in eq2.
      assert (narg = #|args|) as -> by (now apply decompose_stack_at_length in eq2).
      eapply decompose_stack_at_eq in eq2 as ->.
      symmetry in eq4.
      apply decompose_stack_eq in eq4.
      subst.
      rewrite zipc_appstack in h.
      apply Req_red in r as [r].
      cbn in *.
      eapply red_welltyped in h; eauto.
      rewrite zipc_appstack in h.
      cbn in h.
      rewrite tApp_mkApps in h.
      unfold zipp in *.
      apply welltyped_zipc_zipp in h; auto.
      unfold zipp in *.
      rewrite decompose_stack_appstack in *.
      cbn.
      destruct (decompose_stack ρ) eqn:decomp.
      apply decompose_stack_eq in decomp as ->.
      cbn in *.
      rewrite <-mkApps_app in h.
      destruct h as (ty&typ).
      repeat (try rewrite stack_context_appstack;
        try rewrite stack_context_appstack in typ;
        try rewrite stack_context_appstack in haux;
        try rewrite stack_context_appstack in H;
        cbn in * ).
      destruct H as (noapp&_); cbn in *.
      rewrite app_nil_r in *.
      rewrite <- app_assoc in *.
      cbn in *.
      destruct haux.
      symmetry in eq1.
      constructor.
      constructor. unfold unfold_fix in eq1.
      case_eq (nth_error mfix idx); [intros d e | intro e]; rewrite e in eq1; inversion eq1.
      eapply whne_fixapp.
      + eassumption.
      + now apply nth_error_snoc.
      + eapply whnf_fix_arg_whne; eauto.
        * unfold unfold_fix. now rewrite e.
        * now destruct t.
    - unfold zipp.
      destruct decompose_stack.
      constructor.
      apply whnf_mkApps.
      now apply whne_case_noiota.
    - match type of eq with
      | _ = reduce ?x ?y ?z =>
        specialize (haux x y z);
          destruct (reduce x y z)
      end.
      noconf eq; cbn in *.
      pose proof (hΣ _ wfΣ) as [hΣ].
      clear -hΣ wfΣ ht prf' h prf haux.
      destruct (prf _ wfΣ) as (r&stacks&?).
      unfold Pr in stacks.
      cbn in *.
      unfold snd in stacks.
      rewrite <- prf' in stacks.
      subst.
      symmetry in prf'.
      apply decompose_stack_eq in prf' as ->.
      apply Req_red in r as [r].
      cbn in *.
      eapply red_welltyped in h; eauto using sq.
      clear r.
      rewrite zipc_appstack in h.
      cbn in h.
      zip fold in h.
      apply welltyped_context in h; auto.
      cbn in *.
      destruct h as (ty&typ).
      unfold zipp in *.
      rewrite decompose_stack_appstack in haux; cbn in *.

      destruct decompose_stack eqn:decomp.
      apply decompose_stack_eq in decomp as ->.
      repeat (try rewrite stack_context_appstack;
        try rewrite stack_context_appstack in typ;
        try rewrite stack_context_appstack in haux;
        try rewrite stack_context_appstack in H;
        cbn in * ).
      rewrite app_nil_r in *.
      destruct haux.
      constructor.
      apply whnf_mkApps, whne_case.
      eapply whnf_case_arg_whne; eauto.
      destruct H as (noapp&_).
      now destruct t.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π''] Ha eq''. cbn.
      rewrite eq'' in haux. cbn in haux.
      assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π''] Ha eq''. cbn.
      rewrite eq'' in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. eapply whne_proj_noiota. assumption.
    - match type of eq with
      | _ = reduce ?x ?y ?z =>
        specialize (haux x y z);
          destruct (reduce x y z)
      end.
      noconf eq; cbn in *.
      pose proof (hΣ _ wfΣ) as [hΣ].
      clear -hΣ wfΣ ht prf' h prf haux.
      destruct (prf _ wfΣ) as (r&stacks&?).
      unfold Pr in stacks.
      cbn in *.
      unfold snd in stacks.
      rewrite <- prf' in stacks.
      subst.
      symmetry in prf'.
      apply decompose_stack_eq in prf' as ->.
      apply Req_red in r as [r].
      cbn in *.
      eapply red_welltyped in h; eauto using sq.
      clear r.
      rewrite zipc_appstack in h.
      cbn in h.
      zip fold in h.
      apply welltyped_context in h; auto.
      cbn in *.
      destruct h as (ty&typ).
      unfold zipp in *.
      rewrite decompose_stack_appstack in haux; cbn in *.

      destruct decompose_stack eqn:decomp.
      apply decompose_stack_eq in decomp as ->.
      repeat (try rewrite stack_context_appstack;
        try rewrite stack_context_appstack in typ;
        try rewrite stack_context_appstack in haux;
        try rewrite stack_context_appstack in H;
        cbn in * ).
      rewrite app_nil_r in *.
      destruct haux.
      constructor. apply whnf_mkApps, whne_proj.
      eapply whnf_proj_arg_whne; eauto.
      destruct H as (noapp&_).
      now destruct t.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π''] Ha eq'. cbn.
      rewrite eq' in haux. cbn in haux.
      assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π''] Ha eq''. cbn.
      rewrite eq'' in haux. cbn in haux.
      assumption.
  Qed.

  Theorem reduce_term_complete Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t h :
    ∥whnf flags Σ Γ (reduce_term Γ t h)∥.
  Proof using Type.
    pose proof (reduce_stack_whnf Γ t [] h _ wfΣ) as H.
    unfold reduce_term.
    unfold reduce_stack in *.
    destruct reduce_stack_full.
    destruct (a _ wfΣ) as (_&stack_eq&_).
    unfold Pr in stack_eq.
    cbn in stack_eq.
    destruct decompose_stack eqn:decomp.
    cbn in *.
    subst.
    apply decompose_stack_eq in decomp.
    unfold zip, zipp in *.
    destruct x; cbn in *.
    subst s.
    rewrite zipc_appstack.
    rewrite stack_context_appstack, decompose_stack_appstack in H.
    cbn in *.
    now rewrite app_nil_r in H.
  Qed.

End Reduce.

Section ReduceFns.

  Context {cf : checker_flags} {no : normalizing_flags}
          {X_type : abstract_env_impl} {X : X_type.π2.π1} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.

  (* We get stack overflow on Qed after Equations definitions when this is transparent *)
  Opaque reduce_stack_full.

  Definition hnf := reduce_term RedFlags.default X_type X.

  Theorem hnf_sound {Γ t h} Σ (wfΣ : abstract_env_ext_rel X Σ) : ∥ Σ ;;; Γ ⊢ t ⇝ hnf Γ t h ∥.
  Proof using Type.
    unfold hnf.
    destruct (reduce_term_sound RedFlags.default _ X _ _ h Σ wfΣ).
    sq. eapply into_closed_red; fvs.
  Defined.

  Theorem hnf_complete {Γ t h} Σ (wfΣ : abstract_env_ext_rel X Σ) : ∥whnf RedFlags.default Σ Γ (hnf Γ t h)∥.
  Proof using Type.
    apply reduce_term_complete; eauto.
  Qed.

  Equations? reduce_to_sort (Γ : context) (t : term)
    (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t)
    : typing_result_comp (∑ u, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ⇝ tSort u ∥) :=
    reduce_to_sort Γ t h with view_sortc t := {
      | view_sort_sort s => Checked_comp (s; _);
      | view_sort_other t _ with inspect (hnf Γ t h) :=
        | exist hnft eq with view_sortc hnft := {
          | view_sort_sort s => Checked_comp (s; _);
          | view_sort_other hnft r => TypeError_comp (NotASort hnft) _
        }
      }.
  Proof using Type.
    * destruct (h _ wfΣ) as [? hs].
      pose proof (hΣ := hΣ _ X _ wfΣ). sq.
      eapply (wt_closed_red_refl hs).
    * pose proof (hnf_sound (h:=h)).
      now rewrite eq.
    * destruct (abstract_env_ext_exists X) as [[Σ wfΣ]]. specialize (X1 _ wfΣ).
      pose proof (hΣ := hΣ _ X _ wfΣ). sq.
      edestruct (@hnf_complete Γ t h) as [wh]; eauto.
      edestruct (@hnf_sound Γ t h) as [r']; eauto.
      eapply PCUICContextConversion.closed_red_confluence in X1 as (?&r1&r2); eauto.
      apply invert_red_sort in r2 as ->.
      eapply whnf_red_inv in r1; eauto.
      depelim r1.
      rewrite H in r.
      now cbn in r.
  Qed.

  Lemma reduce_to_sort_complete {Γ t wt} Σ (wfΣ : abstract_env_ext_rel X Σ)
    e p :
    reduce_to_sort Γ t wt = TypeError_comp e p ->
    (forall s, red Σ Γ t (tSort s) -> False).
  Proof using Type.
    intros _ s r.
    apply p.
    exists s.
    intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    pose proof (hΣ := hΣ _ X _ wfΣ). sq.
    eapply into_closed_red in r ; fvs.
    Unshelve. eauto.
  Qed.

  Equations? reduce_to_prod (Γ : context) (t : term)
    (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t)
    : typing_result_comp (∑ na a b, forall  Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ⇝ tProd na a b ∥) :=
    reduce_to_prod Γ t h with view_prodc t := {
      | view_prod_prod na a b => Checked_comp (na; a; b; _);
      | view_prod_other t _ with inspect (hnf Γ t h) :=
        | exist hnft eq with view_prodc hnft := {
          | view_prod_prod na a b => Checked_comp (na; a; b; _);
          | view_prod_other hnft _ => TypeError_comp (NotAProduct t hnft) _
        }
      }.
  Proof using Type.
    * destruct (h _ wfΣ) as [? hs].
      pose proof (hΣ := hΣ _ _ _ wfΣ). sq.
      now eapply wt_closed_red_refl.
    * pose proof (hnf_sound (h:=h)).
      now rewrite eq.
    * destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
      specialize (X3 _ wfΣ).
      sq.
      edestruct (@hnf_complete Γ t h) as [wh]; eauto.
      edestruct (@hnf_sound Γ t h) as [r']; eauto.
      destruct (hΣ _ _ _ wfΣ).
      eapply PCUICContextConversion.closed_red_confluence in X3 as (?&r1&r2); eauto.
      apply invert_red_prod in r2 as (?&?&[-> ? ?]); auto.
      eapply whnf_red_inv in r1; auto.
      depelim r1.
      now rewrite H in n0.
  Qed.

  Lemma reduce_to_prod_complete {Γ t wt} Σ (wfΣ : abstract_env_ext_rel X Σ)
    e p :
    reduce_to_prod Γ t wt = TypeError_comp e p ->
    (forall na a b, red Σ Γ t (tProd na a b) -> False).
  Proof using Type.
    intros _ na a b r.
    apply p.
    exists na, a, b.
    intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    pose proof (hΣ := hΣ _ _ _ wfΣ). sq.
    eapply into_closed_red; fvs.
    Unshelve. eauto.
  Qed.

  Equations? reduce_to_ind (Γ : context) (t : term)
    (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t)
    : typing_result_comp (∑ i u l, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ⇝ mkApps (tInd i u) l ∥) :=
    reduce_to_ind Γ t h with inspect (decompose_app t) := {
      | exist (thd, args) eq_decomp with view_indc thd := {
        | view_ind_tInd i u => Checked_comp (i; u; args; _);
        | view_ind_other thd _ with inspect (reduce_stack RedFlags.default _ X Γ t [] h) := {
          | exist (hnft, π) eq with view_indc hnft := {
            | view_ind_tInd i' u with inspect (decompose_stack π) := {
              | exist (l, _) eq_decomp' => Checked_comp (i'; u; l; _)
              };
            | view_ind_other _ _ => TypeError_comp (NotAnInductive t) _
            }
          }
        }
      }.
  Proof using Type.
    - specialize (h _ wfΣ). destruct h  as [? h].
      assert (Xeq : mkApps (tInd i u) args = t).
      { etransitivity. 2: symmetry; eapply mkApps_decompose_app.
        now rewrite <- eq_decomp. }
      rewrite Xeq. pose proof (hΣ := hΣ _ _ _ wfΣ); sq; eapply (wt_closed_red_refl h).
    - pose proof (reduce_stack_sound RedFlags.default _ X _ wfΣ _ _ [] h).
      rewrite <- eq in H.
      cbn in *.
      assert (π = appstack l []) as ->.
      2: { now rewrite zipc_appstack in H. }
      unfold reduce_stack in eq.
      edestruct reduce_stack_full as (?&_&stack_val&?); eauto.
      subst x.
      unfold Pr in stack_val.
      cbn in *.
      assert (decomp: decompose_stack π = ((decompose_stack π).1, [])).
      { rewrite stack_val.
        now destruct decompose_stack. }
      apply decompose_stack_eq in decomp as ->.
      now rewrite <- eq_decomp'.
    - destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
      specialize (X3 _ wfΣ).
      pose proof (hΣ := hΣ _ _ _ wfΣ). sq.
      pose proof (reduce_stack_whnf RedFlags.default _ X Γ t [] h _  wfΣ) as wh.
      unfold reduce_stack in *.
      edestruct reduce_stack_full as ((hd&π')&r'&stack_valid&(notapp&_)); eauto.
      destruct wh as [wh].
      apply Req_red in r' as [r'].
      unfold Pr in stack_valid.
      cbn in *.
      eapply into_closed_red in r'; fvs.
      eapply PCUICContextConversion.closed_red_confluence in r' as (?&r1&r2).
      2 : exact X3.
      assert (exists args, π' = appstack args []) as (?&->).
      { exists ((decompose_stack π').1).
        assert (decomp: decompose_stack π' = ((decompose_stack π').1, [])).
        { now rewrite stack_valid; destruct decompose_stack; cbn. }
        now apply decompose_stack_eq in decomp. }
      unfold zipp in wh.
      rewrite stack_context_appstack, decompose_stack_appstack in wh.
      rewrite zipc_appstack in r2.
      cbn in *.
      rewrite app_nil_r in wh.
      eapply whnf_red_inv in r2; eauto.
      apply invert_red_mkApps_tInd in r1 as (?&[-> _ ?]); auto.
      apply whnf_red_mkApps_inv in r2 as (?&?); auto.
      depelim w.
      noconf eq.
      discriminate i0.
  Qed.

  Lemma reduce_to_ind_complete  Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ty wat e p :
    reduce_to_ind Γ ty wat = TypeError_comp e p ->
    forall ind u args,
      red Σ Γ ty (mkApps (tInd ind u) args) ->
      False.
  Proof using Type.
    intros _ ind u args' r.
    apply p.
    exists ind, u, args'.
    intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    pose proof (hΣ := hΣ _ _ _ wfΣ). sq.
    eapply into_closed_red ; fvs.
    Unshelve. eauto.
  Qed.

  (* Definition of assumption-only arities (without lets) *)
  Definition arity_ass := aname * term.

  Fixpoint mkAssumArity (l : list arity_ass) (s : sort) : term :=
    match l with
    | [] => tSort s
    | (na, A) :: l => tProd na A (mkAssumArity l s)
    end.

  Definition arity_ass_context := rev_map (fun '(na, A) => vass na A).

  Lemma assumption_context_arity_ass_context l :
    assumption_context (arity_ass_context l).
  Proof using Type.
    unfold arity_ass_context.
    rewrite rev_map_spec.
    induction l using MRList.rev_ind; cbn.
    - constructor.
    - rewrite map_app, rev_app_distr.
      cbn.
      destruct x.
      constructor; auto.
  Qed.

  Lemma mkAssumArity_it_mkProd_or_LetIn (l : list arity_ass) (s : sort) :
    mkAssumArity l s = it_mkProd_or_LetIn (arity_ass_context l) (tSort s).
  Proof using Type.
    unfold arity_ass_context.
    rewrite rev_map_spec.
    induction l; auto.
    cbn.
    destruct a.
    rewrite IHl, it_mkProd_or_LetIn_app; auto.
  Qed.

  Lemma isArity_mkAssumArity l s :
    isArity (mkAssumArity l s).
  Proof using Type.
    induction l as [|(na & A) l IH]; cbn; auto.
  Qed.

  Record conv_arity {Γ T} : Type :=
    build_conv_arity {
        conv_ar_context : list arity_ass;
        conv_ar_univ : sort;
        conv_ar_red : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ T ⇝ mkAssumArity conv_ar_context conv_ar_univ ∥
      }.

  Global Arguments conv_arity : clear implicits.

  Lemma conv_arity_Is_conv_to_Arity {Γ T} :
    is_closed_context Γ ->
    is_open_term Γ T ->
    conv_arity Γ T ->
    forall Σ (wfΣ : abstract_env_ext_rel X Σ), Is_conv_to_Arity Σ Γ T.
  Proof using Type.
    intros clΓ clT [asses univ r] Σ wfΣ.
    eexists. destruct (r _ wfΣ). split; [sq|]; tea.
    apply isArity_mkAssumArity.
  Qed.

  Lemma isArity_red Σ Γ u v :
    isArity u ->
    red Σ Γ u v ->
    isArity v.
  Proof using Type.
    intros arity_u r.
    induction r using red_rect_n1; [easy|].
    eapply isArity_red1; eassumption.
  Qed.

  Lemma Is_conv_to_Arity_red Σ {wfΣ : wf Σ} Γ T T' :
    Is_conv_to_Arity Σ Γ T ->
    Σ ;;; Γ ⊢ T ⇝ T' ->
    Is_conv_to_Arity Σ Γ T'.
  Proof using Type.
    unfold Is_conv_to_Arity.
    intros [T'' (redT'' & is_arity)] red.
    sq.
    destruct (PCUICContextConversion.closed_red_confluence red redT'') as (a & reda' & reda'').
    exists a.
    split; [easy|].
    clear -is_arity reda''.
    eapply isArity_red; eauto. exact reda''.
  Qed.

  Local Instance wellfounded Σ wfΣ {normalization:NormalizationIn Σ} : WellFounded (@hnf_subterm_rel _ Σ) :=
    @wf_hnf_subterm _ _ _ normalization (heΣ _ X Σ wfΣ).

End ReduceFns.
