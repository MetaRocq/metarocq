From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Template Require Import Loader All.
Import MonadNotation.
Module Foo.
    Inductive bar : Set := .
  Definition t := nat.
End Foo.

MetaRocq Run (tmQuoteModule "Foo"%bs >>= tmPrint).
MetaRocq Run (tmQuoteModule "Datatypes"%bs >>= tmPrint).

Module Type Typ. Axiom t : Type. End Typ.

Module Outer.
  Module Inner.
    Definition t := nat.
  End Inner.
  Definition t := bool.
  Module Type InnerT.
    Axiom t : Set.
  End InnerT.
  Module InnerF (T : Typ).
    Axiom t : Set.
  End InnerF.
End Outer.

MetaRocq Run (m <- tmQuoteModule "Outer"%bs;; _ <- tmPrint m;; match m ==
                                               [ConstRef
   (MPdot (MPdot (MPfile ["tmQuoteModule"%bs; "TestSuite"%bs; "MetaRocq"%bs]) "Outer"%bs) "Inner"%bs,
    "t"%bs);
 ConstRef (MPdot (MPfile ["tmQuoteModule"%bs; "TestSuite"%bs; "MetaRocq"%bs]) "Outer"%bs, "t"%bs)]%list with true
                                               => ret tt
                                                              | _ => tmFail "bad"%bs
                                                              end).
(** currently QuoteModFunctor means "include functors", maybe it should mean something else? *)
MetaRocq Run (m <- tmQuoteModFunctor "Outer"%bs;; _ <- tmPrint m;; match m ==
                                   [ConstRef
   (MPdot (MPdot (MPfile ["tmQuoteModule"%bs; "TestSuite"%bs; "MetaRocq"%bs]) "Outer"%bs) "Inner"%bs,
    "t"%bs);
 ConstRef (MPdot (MPfile ["tmQuoteModule"%bs; "TestSuite"%bs; "MetaRocq"%bs]) "Outer"%bs, "t"%bs);
 ConstRef
   (MPdot (MPdot (MPfile ["tmQuoteModule"%bs; "TestSuite"%bs; "MetaRocq"%bs]) "Outer"%bs) "InnerF"%bs,
    "t"%bs)]%list
 with true
                                               => ret tt
                                                              | _ => tmFail "bad"%bs
                                                                  end).
(** currently QuoteModType means "include functors and types", but maybe it should mean something else? *)
MetaRocq Run (m <- tmQuoteModType "Outer"%bs;; _ <- tmPrint m;; match m ==
[ConstRef
   (MPdot (MPdot (MPfile ["tmQuoteModule"%bs; "TestSuite"%bs; "MetaRocq"%bs]) "Outer"%bs) "Inner"%bs,
    "t"%bs);
 ConstRef (MPdot (MPfile ["tmQuoteModule"%bs; "TestSuite"%bs; "MetaRocq"%bs]) "Outer"%bs, "t"%bs);
 ConstRef
   (MPdot (MPdot (MPfile ["tmQuoteModule"%bs; "TestSuite"%bs; "MetaRocq"%bs]) "Outer"%bs) "InnerT"%bs,
    "t"%bs);
 ConstRef
   (MPdot (MPdot (MPfile ["tmQuoteModule"%bs; "TestSuite"%bs; "MetaRocq"%bs]) "Outer"%bs) "InnerF"%bs,
    "t"%bs)]%list
 with true
                                               => ret tt
                                                              | _ => tmFail "bad"%bs
                                                              end).
