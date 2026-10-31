From Stdlib Require Import Structures.Equalities Lists.List Lists.ListDec.
From MetaRocq.Utils Require Import MRProd All_Forall ReflectEq MRRelations MRReflect.
From MetaRocq.Common Require Import Environment Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate Require Import (hints) Stdlib.Init Stdlib.ssr utils BasicAst Primitive Universes Kernames.
From MetaRocq.Quotation.ToTemplate.Utils Require Import (hints) MROption MRProd All_Forall.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.

Module Retroknowledge.
  #[export] Instance quote_t : ground_quotable Retroknowledge.t := ltac:(destruct 1; exact _).
  #[export] Instance quote_extends {x y} : ground_quotable (@Retroknowledge.extends x y) := ltac:(cbv [Retroknowledge.extends]; exact _).
End Retroknowledge.
Export (hints) Retroknowledge.

Module QuoteEnvironmentHelper (T : Term) (Import E : EnvironmentSig T).
  Lemma forall_all_helper_iff {Σ Σ' : global_env}
    : (forall c, { decls & lookup_envs Σ' c = (decls ++ lookup_envs Σ c)%list })
        <~> All (fun '(c, _) => { decls & lookup_envs Σ' c = decls ++ lookup_envs Σ c }) (declarations Σ).
  Proof.
    split.
    { intro H.
      apply In_All; intros [c ?] _; specialize (H c); assumption. }
    { intros H c.
      generalize (fun n k H' => @nth_error_all _ _ _ n (c, k) H' H).
      destruct (In_dec Kernames.KernameSet.E.eq_dec c (List.map fst (declarations Σ))) as [H'|H'].
      { induction (declarations Σ) as [|[k ?] xs IH]; cbn in *.
        { exfalso; assumption. }
        { destruct (eqb_specT k c); subst.
          { intro H''; specialize (H'' 0 _ eq_refl); cbn in H''.
            exact H''. }
          { assert (H'' : In c (map fst xs)) by now destruct H'.
            inversion H; subst.
            intro H'''; apply IH; auto.
            intros; eapply (H''' (S _)); cbn; eassumption. } } }
      { unfold lookup_envs in *.
        intros _.
        clear H.
        induction (declarations Σ) as [|x xs IH]; cbn in *.
        { eexists; rewrite List.app_nil_r; reflexivity. }
        { destruct (eqb_specT c x.1); subst.
          { exfalso; intuition. }
          { apply IH.
            intuition. } } } }
  Qed.

  (* quotable versions *)
  Definition extends_alt (Σ Σ' : global_env) :=
    [× Σ.(universes) ⊂_cs Σ'.(universes),
      All (fun '(c, _) => { decls & lookup_envs Σ' c = decls ++ lookup_envs Σ c }) (declarations Σ) &
        Retroknowledge.extends Σ.(retroknowledge) Σ'.(retroknowledge)].

  Definition extends_decls_alt (Σ Σ' : global_env) :=
    [× Σ.(universes) = Σ'.(universes),
      All (fun '(c, _) => { decls & lookup_envs Σ' c = decls ++ lookup_envs Σ c }) (declarations Σ) &
        Σ.(retroknowledge) = Σ'.(retroknowledge)].

  Lemma extends_alt_iff {Σ Σ'} : extends_alt Σ Σ' <~> extends Σ Σ'.
  Proof.
    cbv [extends extends_alt].
    destruct (@forall_all_helper_iff Σ Σ').
    split; intros []; split; auto with nocore.
  Defined.

  Lemma extends_decls_alt_iff {Σ Σ'} : extends_decls_alt Σ Σ' <~> extends_decls Σ Σ'.
  Proof.
    cbv [extends_decls extends_decls_alt].
    destruct (@forall_all_helper_iff Σ Σ').
    split; intros []; split; auto with nocore.
  Defined.
End QuoteEnvironmentHelper.

Module Type QuoteEnvironmentHelperSig (T : Term) (E : EnvironmentSig T) := Nop <+ QuoteEnvironmentHelper T E.

Module Type QuotationOfQuoteEnvironmentHelper (T : Term) (E : EnvironmentSig T) (QEH : QuoteEnvironmentHelperSig T E).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "QEH").
End QuotationOfQuoteEnvironmentHelper.

Module QuoteEnvironment (T : Term) (Import E : EnvironmentSig T) (Import QEH : QuoteEnvironmentHelperSig T E) (Import qT : QuotationOfTerm T) (Import qE : QuotationOfEnvironment T E) (Import qQEH : QuotationOfQuoteEnvironmentHelper T E QEH) (Import QuoteT : QuoteTerm T) <: QuoteEnvironmentSig T E.

  #[export] Hint Unfold
    context
    global_declarations
    global_env_ext
    judgment
  : quotation.
  #[export] Typeclasses Transparent
    context
    global_declarations
    global_env_ext
    judgment
  .

  Import PolymorphicInstances.

  #[export] Instance quote_constructor_body : ground_quotable constructor_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_projection_body : ground_quotable projection_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_one_inductive_body : ground_quotable one_inductive_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_mutual_inductive_body : ground_quotable mutual_inductive_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_constant_body : ground_quotable constant_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_global_decl : ground_quotable global_decl := ltac:(destruct 1; exact _).

  #[export] Instance quote_global_env : ground_quotable global_env := ltac:(destruct 1; exact _).

  #[export] Instance quote_extends_alt {Σ Σ'} : ground_quotable (@extends_alt Σ Σ') := ltac:(cbv [extends_alt]; exact _).
  #[export] Instance quote_extends_decls_alt {Σ Σ'} : ground_quotable (@extends_decls_alt Σ Σ') := ltac:(cbv [extends_decls_alt]; exact _).
  #[export] Instance qextends_alt : quotation_of extends_alt := ltac:(cbv [extends_alt]; exact _).
  #[export] Instance qextends_decls_alt : quotation_of extends_decls_alt := ltac:(cbv [extends_decls_alt]; exact _).

  #[export] Instance quote_extends {Σ Σ'} : ground_quotable (@extends Σ Σ') := ground_quotable_of_iffT extends_alt_iff.
  #[export] Instance quote_extends_decls {Σ Σ'} : ground_quotable (@extends_decls Σ Σ') := ground_quotable_of_iffT (@extends_decls_alt_iff Σ Σ').
  #[export] Instance quote_extends_strictly_on_decls {Σ Σ'} : ground_quotable (@extends_strictly_on_decls Σ Σ') := ltac:(cbv [extends_strictly_on_decls]; exact _).
  #[export] Instance quote_strictly_extends_decls {Σ Σ'} : ground_quotable (@strictly_extends_decls Σ Σ') := ltac:(cbv [strictly_extends_decls]; exact _).

  #[export] Instance quote_primitive_invariants {prim_ty cdecl} : ground_quotable (primitive_invariants prim_ty cdecl) := ltac:(cbv [primitive_invariants]; exact _).

  #[export] Instance quote_All_decls {P t t'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P t t')} : ground_quotable (All_decls P t t') := ltac:(induction 1; exact _).
  #[export] Instance quote_All_decls_alpha {P t t'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P t t')} : ground_quotable (All_decls_alpha P t t') := ltac:(induction 1; exact _).

  Definition quote_context : ground_quotable context := ltac:(cbv [context]; exact _).
  Definition quote_global_env_ext : ground_quotable global_env_ext := ltac:(cbv [global_env_ext]; exact _).
End QuoteEnvironment.
