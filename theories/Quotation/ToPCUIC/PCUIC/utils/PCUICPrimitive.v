From MetaRocq.Utils.MRTactics Require Import DestructHead UniquePose.
From MetaRocq.PCUIC Require Import utils.PCUICPrimitive.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Stdlib.Init Stdlib.Numbers Stdlib.Floats.
From MetaRocq.Quotation.ToPCUIC.Common Require Import (hints) Universes Primitive.
From MetaRocq.Quotation.ToPCUIC.Utils Require Import (hints) All_Forall.

#[export] Instance quote_array_model {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (array_model term) := ltac:(destruct 1; exact _).

#[export] Instance quotation_of_array_model {term a} {qterm : quotation_of term} {qa : @tPrimProp term quotation_of (existT _ Primitive.primArray (primArrayModel a))} : quotation_of a
  := ltac:(cbv -[quotation_of] in qa; destruct a; destruct_head'_prod; exact _).

#[export] Hint Extern 0 (@tPrimProp ?term quotation_of ?a)
=> lazymatch goal with
   | [ H : @tPrimProp _ quotation_of _ |- _ ] => assumption
   | [ H : @tPrimProp _ (fun x => quotation_of x) _ |- _ ] => assumption
   end : typeclass_instances.

#[export] Instance quote_prim_model {term tag} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (prim_model term tag) := ltac:(destruct 1; eauto).

#[export] Instance quote_pstring : ground_quotable PrimString.string := fun s => PCUICAst.tString s.

#[export] Instance quote_prim_model_of {term tag} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (prim_model_of term tag) := ltac:(cbv [prim_model_of]; destruct tag; exact _).

#[export] Instance quote_prim_val {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (prim_val term) := ltac:(cbv [prim_val]; exact _).

#[export] Instance quotation_of_prim_val {term} {p : prim_val term} {qterm : quotation_of term} {qp : @tPrimProp term quotation_of p} : quotation_of p := ltac:(destruct p as [? p]; destruct p; exact _).

Definition quote_onPrims {term eq_term leq_term u u'} {qterm : quotation_of term} {qeq_term : quotation_of eq_term} {qleq_term : quotation_of leq_term}
  {quote_term : ground_quotable term}
  {quote_eq_term : forall x y, ground_quotable (eq_term x y)}
  {quote_leq_term : forall x y, ground_quotable (leq_term x y)} : ground_quotable (@onPrims term eq_term leq_term u u')
  := ltac:(destruct 1; exact _).

Definition quote_onPrims_Type_Prop {term eq_term} {leq_term : _ -> _ -> Prop} {u u'} {qterm : quotation_of term} {qeq_term : quotation_of eq_term} {qleq_term : quotation_of leq_term}
  {quote_term : ground_quotable term}
  {quote_eq_term : forall x y, ground_quotable (eq_term x y)}
  {quote_leq_term : forall x y, ground_quotable (leq_term x y)} : ground_quotable (@onPrims term eq_term leq_term u u')
  := @quote_onPrims term eq_term leq_term u u' qterm qeq_term qleq_term quote_term quote_eq_term quote_leq_term.

Definition quote_onPrims_via_dep
  {term eq_term leq_term u u' p} {eq_term_dep leq_term_dep}
  {qp : @onPrims_dep term eq_term leq_term eq_term_dep leq_term_dep u u' p}
  {qterm : quotation_of term} {qeq_term : quotation_of eq_term} {qleq_term : quotation_of leq_term}
  {quote_term : ground_quotable term}
  {quote_eq_term : forall x y e, eq_term_dep x y e -> quotation_of e}
  {quote_leq_term : forall x y e, leq_term_dep x y e -> quotation_of e}
  : quotation_of p.
Proof.
  destruct qp.
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
  all: repeat (let H := multimatch goal with H : _ |- _ => H end in
               first [ unique pose proof (quote_leq_term _ _ _ H)
                     | unique pose proof (quote_eq_term _ _ _ H) ]).
  all: exact _.
Defined.

#[export] Hint Extern 0 (@quotation_of (@onPrims ?term ?eq_term ?leq_term ?u ?u') ?x)
=> lazymatch goal with
   | [ H : @onPrims_dep _ _ _ ?eq_term_dep ?leq_term_dep _ _ x |- _ ]
     => simple apply (@quote_onPrims_via_dep term eq_term leq_term u u' x eq_term_dep leq_term_dep H)
   | _ => simple apply @quote_ground;
          tryif (lazymatch type of leq_term with
                 | _ -> _ -> Prop => idtac
                 | Relation_Definitions.relation _ => idtac
                 end)
          then simple apply (@quote_onPrims_Type_Prop term eq_term leq_term u u')
          else simple apply (@quote_onPrims term eq_term leq_term u u')
   end
  : typeclass_instances.
#[export] Hint Cut [
    ( _ * )
      quote_ground
      quote_onPrims
  ] : typeclass_instances.
