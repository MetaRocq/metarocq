(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From Stdlib Require Init.

Import MRMonadNotation.

(** This is just printing **)
MetaRocq Test Quote (fun x : nat => x).

MetaRocq Test Quote (fun (f : nat -> nat) (x : nat) => f x).

MetaRocq Test Quote (let x := 2 in x).

MetaRocq Test Quote (fun l : list nat => match l with nil => 0 | cons x l => 1 end).

MetaRocq Test Quote (let x := 2 in
            match x with
              | 0 => 0
              | S n => n
            end).

MetaRocq Test Unquote (Ast.tConstruct (mkInd (MPfile ["Datatypes"; "Init"; "Corelib"], "nat") 0) 0 []).

(** Build a definition **)
Definition d : Ast.term.
  let t := constr:(fun x : nat => x) in
  let k x := refine x in
  quote_term t k.
Defined.

(** Another way **)
MetaRocq Quote Definition d' := (fun x : nat => x).

(** To quote existing definitions **)
Definition id_nat : nat -> nat := fun x => x.

MetaRocq Quote Definition d'' := Eval compute in id_nat.
MetaRocq Quote Definition d3 := Eval cbn in id_nat.
MetaRocq Quote Definition d4 := Eval unfold id_nat in id_nat.


(** Fixpoints **)
Fixpoint add (a b : nat) : nat :=
  match a with
    | 0 => b
    | S a => S (add a b)
  end.
Eval vm_compute in add.

Fixpoint add' (a b : nat) : nat :=
  match b with
    | 0 => a
    | S b => S (add' a b)
  end.

Fixpoint even (a : nat) : bool :=
  match a with
    | 0 => true
    | S a => odd a
  end
with odd (a : nat) : bool :=
  match a with
    | 0 => false
    | S a => even a
  end.

MetaRocq Quote Definition add_syntax := Eval compute in add.

MetaRocq Quote Definition eo_syntax := Eval compute in even.

MetaRocq Quote Definition add'_syntax := Eval compute in add'.

(** Reflecting definitions **)
Check Corelib.Init.Datatypes.nat.
MetaRocq Unquote Definition zero_from_syntax :=
  (Ast.tConstruct (mkInd (MPfile ["Datatypes"; "Init"; "Corelib"], "nat") 0) 0 []).
Set Printing All.
(* the function unquote_kn in reify.ml4 is not yet implemented *)

Print add_syntax.
Print tCase.
Print add_syntax.
Check tCase.
MetaRocq Unquote Definition add_from_syntax := add_syntax.

MetaRocq Unquote Definition eo_from_syntax := eo_syntax.
Print eo_from_syntax.

Local Notation Nat_module := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat").



MetaRocq Unquote Definition two_from_syntax := (Ast.tApp (Ast.tConstruct (Kernames.mkInd Nat_module 0) 1 nil)
   (Ast.tApp (Ast.tConstruct (Kernames.mkInd Nat_module 0) 1 nil)
      (Ast.tConstruct (Kernames.mkInd Nat_module 0) 0 nil :: nil) :: nil)).

MetaRocq Quote Recursively Definition plus_syntax := plus.

MetaRocq Quote Recursively Definition mult_syntax := mult.

MetaRocq Unquote Definition d''_from_syntax := d''.


(** Primitive Projections. *)

Set Primitive Projections.
Record prod' A B : Type :=
  pair' { fst' : A ; snd' : B }.
Arguments fst' {A B} _.
Arguments snd' {A B} _.

MetaRocq Test Quote ((pair' _ _ true 4).(snd')).


(** Reflecting  Inductives *)

Definition one_i : one_inductive_entry :=
{|
  mind_entry_typename := "demoBool";
  mind_entry_arity := tSort Sort.type0;
  mind_entry_consnames := ["demoTrue"; "demoFalse"];
  mind_entry_lc := [tRel 1; tRel 1];
|}.

Definition one_i2 : one_inductive_entry :=
{|
  mind_entry_typename := "demoBool2";
  mind_entry_arity := tSort Sort.type0;
  mind_entry_consnames := ["demoTrue2"; "demoFalse2"];
  mind_entry_lc := [tRel 0; tRel 0];
|}.

Definition mut_i : mutual_inductive_entry :=
{|
  mind_entry_record := None;
  mind_entry_finite := Finite;
  mind_entry_params := [];
  mind_entry_inds := [one_i; one_i2];
  mind_entry_universes := Monomorphic_entry (LevelSet.empty, UnivConstraintSet.empty);
  mind_entry_template := false;
  mind_entry_variance := None;
  mind_entry_private := None;
|}.

MetaRocq Unquote Inductive mut_i.

Definition anonb := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition bnamed n := {| binder_name := nNamed n; binder_relevance := Relevant |}.

Definition mkImpl (A B : term) : term :=
  tProd anonb A B.


Definition one_list_i : one_inductive_entry :=
{|
  mind_entry_typename := "demoList";
  mind_entry_arity := tSort Sort.type0;
  mind_entry_consnames := ["demoNil"; "demoCons"];
  mind_entry_lc := [tApp (tRel 1) [tRel 0];
    mkImpl (tRel 0) (mkImpl (tApp (tRel 2) [tRel 1]) (tApp (tRel 3) [tRel 2]))];
|}.

Definition mut_list_i : mutual_inductive_entry :=
{|
  mind_entry_record := None;
  mind_entry_finite := Finite;
  mind_entry_params := [{| decl_name := bnamed "A"; decl_body := None;
                         decl_type := (tSort Sort.type0) |}];
  mind_entry_inds := [one_list_i];
  mind_entry_universes := Monomorphic_entry (LevelSet.empty, UnivConstraintSet.empty);
  mind_entry_template := false;
  mind_entry_variance := None;
  mind_entry_private := None;
|}.


MetaRocq Unquote Inductive mut_list_i.
(* Print demoList. *)
(** Records *)

Definition one_pt_i : one_inductive_entry :=
{|
  mind_entry_typename := "Point";
  mind_entry_arity := tSort Sort.type0;
  mind_entry_consnames := ["mkPoint"];
  mind_entry_lc := [
    mkImpl (tRel 0) (mkImpl (tRel 1) (tApp (tRel 3) [tRel 2]))];
|}.

Definition mut_pt_i : mutual_inductive_entry :=
{|
  mind_entry_record := Some (Some "pp");
  mind_entry_finite := BiFinite;
  mind_entry_params := [{| decl_name := bnamed "A"; decl_body := None;
                         decl_type := (tSort Sort.type0) |}];
  mind_entry_inds := [one_pt_i];
  mind_entry_universes := Monomorphic_entry ContextSet.empty;
  mind_entry_template := false;
  mind_entry_variance := None;
  mind_entry_private := None;
|}.

MetaRocq Unquote Inductive mut_pt_i.


(*
Inductive demoList (A : Set) : Set :=
    demoNil : demoList A | demoCons : A -> demoList A -> demoList A
*)


(** Putting the above commands in monadic program *)
Notation inat :=
  {| inductive_mind := Nat_module; inductive_ind := 0 |}.
MetaRocq Run (tmBind (tmQuote (3 + 3)) tmPrint).

MetaRocq Run (tmBind (tmQuoteRec add) tmPrint).

MetaRocq Run (tmBind (tmLocate "add") tmPrint).

Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

MetaRocq Run (printInductive "Init.Datatypes.nat").
MetaRocq Run (printInductive "nat").

CoInductive cnat : Set :=  O :cnat | S : cnat -> cnat.
MetaRocq Run (printInductive "cnat").


Definition printConstant (q : qualid) b : TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | ConstRef kn => (tmQuoteConstant kn b) >>= tmPrint
  | _ => tmFail ("[" ^ q ^ "] is not a constant")
  end.

MetaRocq Run (printConstant "add" false).
Fail MetaRocq Run (printConstant "nat" false).

Definition six : nat.
  exact (3 + 3).
Qed.
MetaRocq Run (printConstant "six" true).
MetaRocq Run (printConstant "six" false).

MetaRocq Run (t <- tmLemma "foo4" nat;;
             tmDefinition "foo5" (t + t + 2)).
Next Obligation.
  exact 3.
Defined.
Print foo5.


MetaRocq Run (t <- tmLemma "foo44" nat ;;
             qt <- tmQuote t ;;
             t <- tmEval all t ;;
             tmPrint qt ;; tmPrint t).
Next Obligation.
  exact (3+2).
Defined.



(* MetaRocq Run (tmQuoteInductive "demoList" *)
(*                        >>= tmDefinition "demoList_syntax"). *)
(* Example unquote_quote_id1: demoList_syntax=mut_list_i *)
(* (* demoList was obtained from mut_list_i *). *)
(*   unfold demoList_syntax. *)
(*   unfold mut_list_i. *)
(*     f_equal. *)
(* Qed. *)

MetaRocq Run (tmDefinition "foo4'" nat >>= tmPrint).

(* We can chain the definition. In the following,
 foo5' = 12 and foo6' = foo5' *)
MetaRocq Run (t <- tmDefinition "foo5'" 12 ;;
                     tmDefinition "foo6'" t).

MetaRocq Run (tmLemma "foo51" nat ;;
                     tmLemma "foo61" bool).
Next Obligation.
  exact 3.
Defined.
Next Obligation.
  exact true.
Qed.




Definition printConstant' (name  : qualid): TemplateMonad unit :=
  gr <- tmLocate1 name ;;
  match gr with
  | ConstRef kn => X <- tmUnquote (tConst kn []) ;;
                  X' <- tmEval all (my_projT2 X) ;;
                  tmPrint X'
  | _ => tmFail ("[" ^ name ^ "] is not a constant")
  end.

Fail MetaRocq Run (printInductive "Stdlib.Arith.PeanoNat.Nat.add").
MetaRocq Run (printConstant' "Stdlib.Arith.PeanoNat.Nat.add").


Fail MetaRocq Run (tmUnquoteTyped (nat -> nat) add_syntax >>= tmPrint).
MetaRocq Run (tmUnquoteTyped (nat -> nat -> nat) add_syntax >>= tmPrint).




Inductive NonRec (A:Set) (C: A -> Set): Set :=
| SS : forall (f:A), C f -> NonRec A C.

MetaRocq Run (printInductive "NonRec").


Set Printing Universes.
Monomorphic Definition Funtm (A B: Type) := A->B.
Polymorphic Definition Funtp@{i} (A B: Type@{i}) := A->B.
(* MetaRocq Run (printConstant "Top.demo.Funtp"). *)
(* Locate Funtm. *)
(* MetaRocq Run (printConstant "Top.Funtm"). *)

Polymorphic Definition Funtp2@{i j}
   (A: Type@{i}) (B: Type@{j}) := A->B.
(* MetaRocq Run (printConstant "Top.demo.Funtp2"). *) (* TODOO *)

MetaRocq Run (tmEval cbn add_syntax >>= tmMkDefinition "foo1").

MetaRocq Run ((tmFreshName "foo") >>= tmPrint).
MetaRocq Run (tmAxiom "foo0" (nat -> nat) >>= tmPrint).
MetaRocq Run (tmAxiom "foo0'" (nat -> nat) >>=
                     fun t => tmDefinition "foo0''" t).
MetaRocq Run (tmFreshName "foo" >>= tmPrint).

MetaRocq Run (tmBind (tmLocate "foo") tmPrint).
MetaRocq Run (tmBind (tmLocate "qlsnkqsdlfhkdlfh") tmPrint).
MetaRocq Run (tmBind (tmLocate "eq") tmPrint).
MetaRocq Run (tmBind (tmLocate "Logic.eq") tmPrint).
MetaRocq Run (tmBind (tmLocate "eq_refl") tmPrint).

MetaRocq Run (tmCurrentModPath tt >>= tmPrint).

MetaRocq Run (tmBind (tmEval all (3 + 3)) tmPrint).
MetaRocq Run (tmBind (tmEval hnf (3 + 3)) tmPrint).

Fail MetaRocq Run (tmFail "foo" >>= tmQuoteInductive).


(* Definition duplicateDefn (name newName : ident): TemplateMonad unit := *)
(*   (tmBind (tmQuote name false) (fun body => *)
(*     match body with *)
(*     | Some (inl (DefinitionEntry {| definition_entry_body := bd |})) => *)
(*         (tmBind (tmPrint body) (fun _ => tmMkDefinition newName bd)) *)
(*     | _ => tmReturn tt *)
(*     end)) *)
(*     . *)

(* MetaRocq Run (duplicateDefn "add" "addUnq"). *)
(* Check (eq_refl: add=addUnq). *)



(** Universes *)

Set Printing Universes.
MetaRocq Test Quote Type.
MetaRocq Test Quote Set.
MetaRocq Test Quote Prop.

Inductive T : Type :=
  | toto : Type -> T.
MetaRocq Quote Recursively Definition TT := T.

Unset MetaRocq Strict Unquote Universe Mode.
MetaRocq Unquote Definition t := (tSort (sType (Universe.of_level (Level.level "Top.20000")))).
MetaRocq Unquote Definition t' := (tSort (sType fresh_universe)).
MetaRocq Unquote Definition myProp := (tSort sProp).
MetaRocq Unquote Definition mySet := (tSort (sType (Universe.of_level Level.lzero))).

(** Cofixpoints *)
CoInductive streamn : Set :=
  scons : nat -> streamn -> streamn.

CoFixpoint ones : streamn := scons 1 ones.

MetaRocq Quote Definition ones_syntax := Eval compute in ones.

MetaRocq Unquote Definition ones' := ones_syntax.

Check eq_refl : ones = ones'.


(* Too long *)
(* MetaRocq Run (tmQuoteUniverses tt >>= tmDefinition "universes"). *)
(* Print universes. *)
(* Definition tyu := Eval vm_compute in universes. *)


Definition kername_of_qualid (q : qualid) : TemplateMonad kername :=
  gr <- tmLocate1 q ;;
  match gr with
  | ConstRef kn  => ret kn
  | IndRef ind => ret ind.(inductive_mind)
  | ConstructRef ind _ => ret ind.(inductive_mind)
  | VarRef _ => tmFail ("tmLocate: " ^ q ^ " is a Var")
  end.

MetaRocq Run (kername_of_qualid "add" >>= tmPrint).
MetaRocq Run (kername_of_qualid "BinNat.N.add" >>= tmPrint).
MetaRocq Run (kername_of_qualid "Stdlib.NArith.BinNatDef.N.add" >>= tmPrint).
MetaRocq Run (kername_of_qualid "N.add" >>= tmPrint).
Fail MetaRocq Run (kername_of_qualid "qlskf" >>= tmPrint).
