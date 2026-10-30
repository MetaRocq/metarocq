From MetaRocq.Quotation.ToTemplate Require Import Stdlib.Init.
From MetaRocq.Utils Require Import MROption MRRelations.

#[local] Hint Extern 0 => reflexivity : typeclass_instances.

#[export] Instance quote_ForOption {A P o} {qA : quotation_of A} {qP : quotation_of P} {qo : quotation_of o} {quoteP : forall t, o = Some t -> ground_quotable (P t:Prop)} : ground_quotable (@ForOption A P o).
Proof.
  destruct o; adjust_ground_quotable_by_econstructor_inversion (); eauto.
Defined.

#[export] Instance quote_option_extends {A o1 o2} {qA : quotation_of A} {qo1 : quotation_of o1} {qo2 : quotation_of o2} {quoteA : forall t, o2 = Some t -> quotation_of t} : ground_quotable (@option_extends A o1 o2).
Proof.
  destruct o1 as [a|], o2 as [a'|].
  all: try specialize (quoteA _ eq_refl).
  all: try solve [ intro pf; exfalso; inversion pf ].
  all: try (intro pf; assert (a = a') by (now inversion pf); subst;
            let t := type of pf in
            revert pf; change (ground_quotable t)).
  all: adjust_ground_quotable_by_econstructor_inversion ().
Defined.

#[export] Polymorphic Instance quote_option_default {A P o b} {quoteP : forall x, o = Some x -> ground_quotable (P x)} {quoteP' : o = None -> ground_quotable b} : ground_quotable (@option_default A Type P o b) := ltac:(destruct o; cbv [option_default]; exact _).
#[export] Polymorphic Instance quote_option_defaultP {A o} {P : A -> Prop} {b : Prop} {quoteP : forall x, o = Some x -> ground_quotable (P x)} {quoteP' : o = None -> ground_quotable b} : ground_quotable (@option_default A Prop P o b) := ltac:(destruct o; cbv [option_default]; exact _).

#[export] Instance quote_on_Some {A P o} {quoteP : forall x, o = Some x -> ground_quotable (P x:Prop)} : ground_quotable (@on_Some A P o) := ltac:(destruct o; cbv [on_Some]; exact _).
#[export] Typeclasses Opaque on_Some.
#[export] Instance quote_on_Some_or_None {A P o} {quoteP : forall x, o = Some x -> ground_quotable (P x:Prop)} : ground_quotable (@on_Some_or_None A P o) := ltac:(destruct o; cbv [on_Some_or_None]; exact _).
#[export] Typeclasses Opaque on_Some_or_None.
#[export] Instance quote_on_some {A P o} {quoteP : forall x, o = Some x -> ground_quotable (P x)} : ground_quotable (@on_some A P o) := ltac:(destruct o; cbv [on_some]; exact _).
#[export] Typeclasses Opaque on_some.
#[export] Instance quote_on_some_or_none {A P o} {quoteP : forall x, o = Some x -> ground_quotable (P x)} : ground_quotable (@on_some_or_none A P o) := ltac:(destruct o; cbv [on_some_or_none]; exact _).
#[export] Typeclasses Opaque on_some_or_none.
Lemma on_Some_or_None_iff_forall {A P o} : @on_Some_or_None A P o <-> (forall x, o = Some x -> P x).
Proof. destruct o; cbn; firstorder try congruence. Qed.
#[export] Instance quote_forall_eq_Some_impl {A P o} {qA : quotation_of A} {qP : quotation_of P} {qo : quotation_of o} {quoteP : forall x, o = Some x -> ground_quotable (P x:Prop)} : ground_quotable (forall x, o = Some x -> P x) | 10
  := ground_quotable_of_iff (@on_Some_or_None_iff_forall A P o).
Lemma on_some_or_none_iff_forall {A P o} : @on_some_or_none A P o <~> (forall x, o = Some x -> P x).
Proof. destruct o; cbn; firstorder try congruence. Qed.
#[export] Polymorphic Instance quote_forall_eq_some_impl {A P o} {qA : quotation_of A} {qP : quotation_of P} {qo : quotation_of o} {quoteP : forall x, o = Some x -> ground_quotable (P x)} : ground_quotable (forall x, o = Some x -> P x) | 20
  := ground_quotable_of_iffT (@on_some_or_none_iff_forall A P o).
