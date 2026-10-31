From MetaRocq.PCUIC Require Import PCUICAst PCUICCumulativitySpec.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Stdlib.Init Stdlib.Lists.
From MetaRocq.Quotation.ToPCUIC.Utils Require Import (hints) All_Forall.
From MetaRocq.Quotation.ToPCUIC.Common Require Import (hints) config BasicAst Universes Kernames.
From MetaRocq.Quotation.ToPCUIC.PCUIC Require Import (hints) PCUICAst PCUICEquality utils.PCUICPrimitive.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

#[export] Instance quote_cumul_predicate {cumul Γ Re p p'} {qcumul : quotation_of cumul} {qRe : quotation_of Re} {quote_cumul : forall x y Γ, ground_quotable (cumul Γ x y)} {quote_Re : forall x y, ground_quotable (Re x y:Prop)} : ground_quotable (@cumul_predicate cumul Re Γ p p')
:= ltac:(cbv [cumul_predicate]; exact _).

#[export] Instance quote_cumul_branch {cumul Γ p br br'} {qcumul : quotation_of cumul} {quote_cumul : forall x y Γ, ground_quotable (cumul Γ x y)} : ground_quotable (@cumul_branch cumul Γ p br br')
:= ltac:(cbv [cumul_branch]; exact _).

#[export] Instance quote_cumul_mfixpoint {cumul Γ mfix mfix'} {qcumul : quotation_of cumul} {quote_cumul : forall x y Γ, ground_quotable (cumul Γ x y)} : ground_quotable (@cumul_mfixpoint cumul Γ mfix mfix')
:= ltac:(cbv [cumul_mfixpoint]; exact _).

Definition quote_cumul_predicate_via_dep {cumul Γ Re Re' p p'} {c : @cumul_predicate cumul Re Γ p p'} (qc : cumul_predicate_dep c (fun _ _ _ c => quotation_of c) Re') {qcumul : quotation_of cumul} {qRe : quotation_of Re} {quote_Re : forall x y, ground_quotable (Re x y:Prop)} : quotation_of c.
Proof.
  cbv [cumul_predicate cumul_predicate_dep] in *.
  repeat match goal with H : _ * _ |- _ => destruct H end.
  exact _.
Defined.
#[export] Hint Extern 0 (cumul_predicate_dep _ (fun _ _ _ r => quotation_of r) _) => eassumption : typeclass_instances.

#[export] Hint Extern 0 (@quotation_of (@cumul_predicate ?cumul ?Re ?Γ ?p ?p') ?x)
=> lazymatch goal with
   | [ H : cumul_predicate_dep x (fun _ _ _ r => quotation_of r) ?Re' |- _ ]
     => simple eapply (@quote_cumul_predicate_via_dep cumul Γ Re Re' p p' x H)
   | _
     => simple apply @quote_ground;
        simple apply (@quote_cumul_predicate cumul Γ Re p p')
   end : typeclass_instances.
#[export] Hint Cut [
    ( _ * )
      quote_ground
      quote_cumul_predicate
  ] : typeclass_instances.

#[export] Hint Unfold
  cumul_Ind_univ
  cumul_Construct_univ
  : quotation.
#[export] Typeclasses Transparent
  cumul_Ind_univ
  cumul_Construct_univ
.

#[export] Instance quote_cumulSpec0 {cf Σ Γ pb t u} : ground_quotable (@cumulSpec0 cf Σ Γ pb t u).
Proof.
  pose proof (compare_universe_subrel Σ : forall pb, RelationClasses.subrelation (compare_universe Σ Conv) (compare_universe Σ pb)).
  induction 1.
  all: unfold cumul_branches, cumul_branch, cumul_mfixpoint in *.
  all: lazymatch goal with
       | [ H : All_Forall.All2_dep ?T ?x |- _ ]
         => lazymatch T with
            | (fun _ _ r => quotation_of r) => idtac
            | _
              => assert (All_Forall.All2_dep (fun _ _ r => quotation_of r) x);
                 [ eapply All_Forall.All2_dep_impl; try exact H; [];
                   cbv beta; intros;
                   repeat match goal with
                     | [ H : _ * _ |- _ ] => destruct H
                     end;
                   cbn [fst snd] in *
                 | clear H ]
            end
       | _ => idtac
       end.
  all: repeat (let v := lazymatch goal with |- quotation_of ?v => v end in
               match v with
               | context[?x]
                 => is_var x; assert_fails constr_eq x v;
                    lazymatch goal with
                    | [ H : quotation_of x |- _ ] => fail
                    | _ => let qx := fresh "q" x in
                           assert (qx : quotation_of x)
                    end
               end).
  Time all: [ > try exact _ .. ].
Defined.

#[export] Hint Unfold
  convSpec
  cumulSpec
  : quotation.
#[export] Typeclasses Transparent
  convSpec
  cumulSpec
.

Definition quote_cumulSpec {cf Σ Γ t u} : ground_quotable (@cumulSpec cf Σ Γ t u) := _.
Definition quote_convSpec {cf Σ Γ t u} : ground_quotable (@convSpec cf Σ Γ t u) := _.

Module QuotePCUICConversionParSpec <: QuoteConversionParSig PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversionParSpec.
  #[export] Instance quote_cumul_gen {cf Σ Γ pb t t'} : ground_quotable (@PCUICConversionParSpec.cumul_gen cf Σ Γ pb t t') := ltac:(cbv [PCUICConversionParSpec.cumul_gen]; exact _).
End QuotePCUICConversionParSpec.
Export (hints) QuotePCUICConversionParSpec.
