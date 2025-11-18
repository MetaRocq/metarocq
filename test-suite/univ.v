From MetaRocq.Template Require Import All.
From Stdlib Require Import List Arith.
Import ListNotations MRMonadNotation.
Open Scope bs_scope.

Notation "'unfolded' d" :=
  ltac:(let y := eval unfold d in d in exact y) (at level 100, only parsing).

Definition cp (s : string) := (MPfile ["univ"; "TestSuite"; "MetaRocq"], s).


Set Printing Universes.

(* Quoting *)
(* MetaRocq Test Quote Type. *)
MetaRocq Quote Definition a_random_univ := Type.

Example a_random_univ_ex :
  exists l, a_random_univ =
            tSort (sType (Universe.of_level (Level.level l))).
Proof. eexists. reflexivity. Qed.

(* Back and forth *)
Definition univ_foo := Type.
(* Print univ_foo. *)
MetaRocq Quote Definition univ_foo_syn := (unfolded univ_foo).
MetaRocq Unquote Definition univ_foo_back := univ_foo_syn.

(* Check eq_refl : univ_foo = univ_foo_back. *)

(* Print univ_foo_back. *)

Fail MetaRocq Unquote Definition t1 := (tSort (sType (Universe.of_level (Level.level "Top.400")))).
(* Fails with "Level Top.<something> not a declared level and you are in Strict Unquote Universe Mode." *)

Unset MetaRocq Strict Unquote Universe Mode.
MetaRocq Unquote Definition t2 := (tSort (sType fresh_universe)).
MetaRocq Unquote Definition t3 := (tSort (sType (Universe.of_level (Level.level "Top.400")))).

Monomorphic Universe i j.

Set MetaRocq Strict Unquote Universe Mode.
MetaRocq Quote Definition testij := (Type@{j} -> Type@{i}).
MetaRocq Unquote Definition T'' := (tSort (sType (Universe.of_level (Level.level "j")))).
Unset MetaRocq Strict Unquote Universe Mode.


Polymorphic Definition pidentity {A : Type} (a : A) := a.
MetaRocq Quote Definition pidentity_syn := (unfolded @pidentity).
MetaRocq Unquote Definition pidentity_back := pidentity_syn.
(* NOTE: The unquoted definition is not polymorphic!*)

MetaRocq Quote Definition pidentityq := @pidentity.
Polymorphic Definition selfpid := pidentity (@pidentity).
MetaRocq Quote Definition selfpidq := @selfpid.

Constraint i < j.

MetaRocq Unquote Definition yuyu :=
  (tConst (cp "selfpid") (Instance.of_level_instance [Level.level "j"; Level.level "i"])).


MetaRocq Quote Definition t0 := nat.
(* MetaRocq Run (tmUnquoteTyped Type t0). *)
Definition ty : Type := Type.
(* MetaRocq Run (tmUnquoteTyped ty t0). *)

Polymorphic Cumulative Inductive test := .
Polymorphic Cumulative Record packType := {pk : Type}.
(* MetaRocq Run (α <- tmQuoteInductive (cp "test") ;; tmPrint α). *)
(* MetaRocq Run (tmQuoteInductive (cp "packType") >>= tmEval all >>= tmPrint). *)


Polymorphic Cumulative Record Category@{i j} :=
{ Obj : Type@{i}; Hom : Obj -> Obj -> Type@{j} }.
Polymorphic  Record Functor@{i j} (C D : Category@{i j}):=
{ ObjF : C.(Obj) -> D.(Obj) }.
Polymorphic Definition Cat@{i j k l} : Category@{i j}
 := Build_Category@{i j} Category@{k l} Functor@{k l}.

(* MetaRocq Run (tmQuoteInductive (cp "Category") >>= tmEval all >>= tmPrint). *)
(* MetaRocq Run (tmQuoteConstant (cp "Cat") false >>= tmEval all >>= tmPrint). *)


Polymorphic Cumulative Inductive list (A : Type) : Type :=
nil : list A | cons : A -> list A -> list A.

Set Printing Universes.

Definition clean_universes_entry e :=
  match e with
  | Monomorphic_entry e => Monomorphic_entry e
  | Polymorphic_entry (names, ci) => Polymorphic_entry (map (fun x => nAnon) names, ci)
  end.

Definition clean_universes_decl (m : mutual_inductive_entry) : mutual_inductive_entry :=
  {| mind_entry_record := m.(mind_entry_record);
    mind_entry_finite := m.(mind_entry_finite);
    mind_entry_params := m.(mind_entry_params);
    mind_entry_inds := m.(mind_entry_inds);
    mind_entry_universes := clean_universes_entry m.(mind_entry_universes);
    mind_entry_template := m.(mind_entry_template);
    mind_entry_variance := m.(mind_entry_variance);
    mind_entry_private := m.(mind_entry_private) |}.

Module to.
 MetaRocq Run (t <- tmQuoteInductive (cp "list") ;;
              t <- tmEval all (mind_body_to_entry t) ;;
              tmMkInductive false (clean_universes_decl t)).

 (* Print list. *)
End to.


Definition f@{i j k} := fun (E:Type@{i}) => Type@{max(i,j)}.
MetaRocq Quote Definition qf := Eval cbv in f.
MetaRocq Unquote Definition uqf := qf.


Inductive foo (A : Type) : Type :=
| fooc : list A -> foo A.
(* Print Universes.*)
(* Top.1 <= Stdlib.Init.Datatypes.44 *)

MetaRocq Quote Recursively Definition qfoo := foo.
(* Compute qfoo. *)

Polymorphic Inductive foo2 (A : Type) : Type :=
| fooc2 : list A -> foo2 A.
(* Top.4 |= Top.4 <= Stdlib.Init.Datatypes.44 *)
(* Print Universes.*)

Definition foo2_instance := foo2.
(* Print Universes.*)
(* Top.9 <= Stdlib.Init.Datatypes.44 *)

MetaRocq Quote Recursively Definition qfoo2 := foo2.
(* Compute qfoo2. *)
(* (Level.lvar 0, Le, Level.level "Stdlib.Init.Datatypes.44") *)

Polymorphic Inductive foo3@{i j k l} (A : Type@{i}) (B : Type@{j}) : Type@{k} :=
| fooc3 : @eq Type@{l} (list A) B-> foo3 A B.
(* i j k l |= l < Stdlib.Init.Logic.8
              Set <= l
              i <= l
              i <= Stdlib.Init.Datatypes.44
              j <= l *)
MetaRocq Quote Recursively Definition qfoo3 := foo3.
(* Compute qfoo3. *)

From MetaRocq Require Import Utils.monad_utils. Import MRMonadNotation.
From MetaRocq Require Import Template.TemplateMonad.Core.

(* MetaRocq Run (tmQuoteInductive (cp "foo") >>= tmPrint).
MetaRocq Run (tmQuoteInductive (cp "foo2") >>= tmPrint).
MetaRocq Run (tmQuoteInductive (cp "foo3") >>= tmPrint). *)

Polymorphic Definition TT@{i j} : Type@{j} := Type@{i}.
MetaRocq Quote Recursively Definition qTT := TT.

Polymorphic Inductive TT2@{i j} : Type@{j} := tt2 : Type@{i} -> TT2.
MetaRocq Quote Recursively Definition qTT2 := TT2.

From MetaRocq Require Import Utils.utils.
From Stdlib Require Import List. Import ListNotations.

Module toto.

  (* MetaRocq Run (en <- tmEval all (mind_body_to_entry (Build_minductive_decl 0 [{| *)
  (*  ind_name := "TT2"; *)
  (*  ind_type := tSort ((Level.lvar 1, false) :: nil)%list; *)
  (*  ind_kelim := InProp :: (InSet :: InType :: nil)%list; *)
  (*  ind_ctors := ("tt2", *)
  (*               tProd nAnon (tSort ((Level.lvar 0, false) :: nil)%list) (tRel 1), *)
  (*               1) :: nil; *)
  (*  ind_projs := nil |}] (UContext.make (Level.lvar 0 :: Level.lvar 1 :: nil)%list *)
  (*    (UnivConstraintSet.add (make_univ_constraint (Level.lvar 0) Lt (Level.lvar 1)) *)
  (*       UnivConstraintSet.empty)))) ;; *)

End toto.


Definition test2 := (fun (T : Type@{i}) (T2 : Type@{j}) => T -> T2).
Set Printing Universes.
(* Print test. *)

Unset Printing Universes.

MetaRocq Quote Definition qtest := Eval compute in (fun (T : Type@{i}) (T2 : Type@{j}) => T -> T2).
(* Print qtest. *)

MetaRocq Unquote Definition bla := qtest.

Definition nNamedR (s : string) := mkBindAnn (nNamed s) Relevant.
Definition nAnonR := mkBindAnn nAnon Relevant.

Unset MetaRocq Strict Unquote Universe Mode.
MetaRocq Unquote Definition bla' := (tLambda (nNamedR "T") (tSort (sType (Universe.of_level (Level.level "Top.46")))) (tLambda (nNamedR "T2") (tSort (sType (Universe.of_level (Level.level "Top.477")))) (tProd nAnonR (tRel 1) (tRel 1)))).

(*
Set Printing Universes.
Print bla.
Print bla'.
Print Universes.
Unset Printing Universes.
*)
Set Universe Polymorphism.

Section test.
  Universe u v.

  Definition t@{u v} : _ -> _ -> Type@{max(u,v)}:=  (fun (T : Type@{u}) (T2 : Type@{v}) => T -> T2).
  (* Set Printing Universes. *)
  (* Print t. *)


End test.

(* Compute t.
Compute (@t Type@{i} Type@{j}). *)

MetaRocq Quote Definition qt := Eval compute in t.
(* Print qt. *)

MetaRocq Unquote Definition t' := qt.

Polymorphic Definition Funtp@{i} (A B: Type@{i}) := A->B.

Polymorphic Definition F@{i} := Type@{i}.

MetaRocq Quote Definition qT := Eval compute in F.
From Stdlib Require Import List. Import ListNotations.
(* NOTE: the command below doesn't work -- gives Error: Anomaly "Universe Var(1) undefined." *)
(* Fail MetaRocq Unquote Definition T'2 := *)
(*   (tSort (Universe.make (Level.lvar 1))). *)

MetaRocq Quote Recursively Definition qT' := F.

MetaRocq Quote Definition qFuntp := Eval compute in Funtp.
(* Print qFuntp. *)
(** the same thing is quoted in demo.v using the template-rocq monad
there the poly vars actually show up *)


Monomorphic Universe i1 j1.
Definition f' := (forall (A:Type@{i1}) (B: Type@{j1}), A -> B -> A).
(* Check f' *)
(* : Type@{max(i1+1, j1+1)} *)

MetaRocq Quote Recursively Definition ff := f'.

(* Require Import MetaRocq.Checker.All. *)
(* Compute (infer' (empty_ext (fst ff)) [] (snd ff)). *)
(* Check (eq_refl : infer' (empty_ext (fst ff)) [] (snd ff) = *)
(*          Checked (tSort (Universe.from_kernel_repr (Level.level _, true) [(Level.level _, true)]))). *)
(* Open Scope string_scope. *)
(* Check (eq_refl : infer [] init_graph [] ((tProd (nNamed "A") (tSort (Universe.make (Level.level _))) (tProd (nNamed "B") (tSort (Universe.make (Level.level _))) (tProd nAnon (tRel 1) (tProd nAnon (tRel 1) (tRel 3)))))) = Checked (tSort _)). *)

