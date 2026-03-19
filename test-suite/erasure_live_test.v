From Stdlib Require Import Recdef.

From MetaRocq.Template Require Import TemplateMonad Loader.
(* From MetaRocq.SafeChecker Require Import SafeTemplateChecker. *)
From MetaRocq.PCUIC Require Import PCUICEquality PCUICAst PCUICReflect PCUICSafeLemmata PCUICTyping PCUICNormal PCUICAstUtils PCUICSN.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC PCUICToTemplate.

From MetaRocq.ErasurePlugin Require Import Erasure.

From Stdlib Require Import String.
Local Open Scope string_scope.

From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Common Require Import config.
Import MonadNotation.
Unset MetaRocq Debug.
(* We're doing erasure assuming no Prop <= Type rule and lets can appear in constructor types. *)
#[local] Existing Instance config.extraction_checker_flags.

Definition test (p : Ast.Env.program) : string :=
  erase_and_print_template_program default_erasure_config [] p.

Definition testty (p : Ast.Env.program) : string :=
  typed_erase_and_print_template_program p.

MetaRocq Quote Recursively Definition zero := 0.

Definition zerocst := Eval lazy in test zero.

MetaRocq Quote Recursively Definition exproof := I.
Definition exprooftest := Eval lazy in test exproof.

MetaRocq Quote Recursively Definition exintro := (@exist _ _ 0 (@eq_refl _ 0) : {x : nat | x = 0}).
Definition exintrotest := Eval lazy in test exintro.

Definition ex_type_introtest := Eval lazy in testty exintro.

Definition id := fun (X : Set) (x : X) => x.
Definition idnat := (id nat).

MetaRocq Quote Recursively Definition idnatc := idnat.
Time Definition test_idnat := Eval lazy in test idnatc.
Time Definition testty_idnat := Eval lazy in testty idnatc.

(** Check that optimization of singleton pattern-matchings work *)
Definition singlelim := ((fun (X : Set) (x : X) (e : x = x) =>
                  match e in eq _ x' return bool with
                  | eq_refl => true
                  end)).

Definition erase {A} (a : A) : TemplateMonad unit :=
  aq <- tmQuoteRec a ;;
  s <- tmEval lazy (erase_and_print_template_program default_erasure_config [] aq) ;;
  tmMsg s.

MetaRocq Run (erase 0).
MetaRocq Run (tmEval hnf idnat >>= erase).
MetaRocq Run (tmEval hnf singlelim >>= erase).
MetaRocq Run (erase (plus 0 1)).

(** vector addition **)
Require Stdlib.Vectors.Vector.

Definition vplus {n:nat} :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := (vplus v01 v23).

Set MetaRocq Timing.

Time MetaRocq Run (tmEval hnf vplus0123 >>= erase).

(** Cofix *)
From Stdlib Require Import StreamMemo.

MetaRocq Quote Recursively Definition memo := memo_make.

Definition testmemo := Eval lazy in test memo.

(** Cofix *)
From Stdlib Require Import StreamMemo.

(** Ackermann **)
Fixpoint ack (n m:nat) {struct n} : nat :=
  match n with
    | 0 => S m
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ack p 1
                   | S q => ack p (ackn q)
                 end
             in ackn m
  end.
Definition ack35 := (ack 3 5).
MetaRocq Quote Recursively Definition cbv_ack35 :=
  ltac:(let t:=(eval cbv delta [ack35] in ack35) in exact t).

Time Definition testack35 := Eval lazy in test cbv_ack35.

(* [program] of the program *)
MetaRocq Quote Recursively Definition p_ack35 := ack35.

Time Definition testack352 := Eval lazy in test p_ack35. (* 0.041 *)

(** mutual recursion **)
Inductive tree (A:Set) : Set :=
  node : A -> forest A -> tree A
with forest (A:Set) : Set :=
     | leaf : A -> forest A
     | fcons : tree A -> forest A -> forest A.
Arguments leaf {A}.
Arguments fcons {A}.
Arguments node {A}.
Definition sf: forest bool := (fcons (node true (leaf false)) (leaf true)).
MetaRocq Quote Recursively Definition p_sf := sf.
Time Definition testp_sf := Eval lazy in test p_sf.

Fixpoint tree_size (t:tree bool) : nat :=
  match t with
    | node a f => S (forest_size f)
  end
with forest_size (f:forest bool) : nat :=
       match f with
         | leaf b => 1
         | fcons t f1 => (tree_size t + forest_size f1)
       end.

Definition arden: forest bool :=
  fcons (node true (fcons (node true (leaf false)) (leaf true)))
        (fcons (node true (fcons (node true (leaf false)) (leaf true)))
               (leaf false)).
MetaRocq Quote Recursively Definition p_arden := arden.
Definition arden_size := (forest_size arden).
MetaRocq Quote Recursively Definition cbv_arden_size :=
  ltac:(let t:=(eval cbv in arden_size) in exact t).
Definition ans_arden_size :=
 Eval lazy in test cbv_arden_size.
(* [program] of the program *)
MetaRocq Quote Recursively Definition p_arden_size := arden_size.

Definition P_arden_size := Eval lazy in test p_arden_size.

(** SASL tautology function: variable arity **)
From Stdlib Require Import Bool.
Fixpoint tautArg (n:nat) : Type :=
  match n with
    | 0 => bool
    | S n => bool -> tautArg n
  end.
Fixpoint taut (n:nat) : tautArg n -> bool :=
  match n with
    | 0 => (fun x => x)
    | S n => fun x => taut n (x true) && taut n (x false)
  end.
(* Pierce *)
Definition pierce := taut 2 (fun x y => implb (implb (implb x y) x) x).
MetaRocq Quote Recursively Definition cbv_pierce :=
  ltac:(let t:=(eval cbv in pierce) in exact t).

Definition ans_pierce :=
  Eval lazy in (test cbv_pierce).

(* [program] of the program *)
MetaRocq Quote Recursively Definition p_pierce := pierce.

Definition P_pierce := Eval lazy in test p_pierce.

(* Goal
  let env := (env P_pierce) in
  let main := (main P_pierce) in
  wcbvEval (env) 200 (main) = Ret ans_pierce.
  vm_compute. reflexivity.
Qed.
 *)(* S combinator *)
Definition Scomb := taut 3
         (fun x y z => implb (implb x (implb y z))
                             (implb (implb x y) (implb x z))).
MetaRocq Quote Recursively Definition cbv_Scomb :=
  ltac:(let t:=(eval cbv in Scomb) in exact t).

Definition ans_Scomb :=
  Eval lazy in (test cbv_Scomb).

(* [program] of the program *)
MetaRocq Quote Recursively Definition p_Scomb := Scomb.

Definition P_Scomb := Eval lazy in (test p_Scomb).

(* Goal
  let env := (env P_Scomb) in
  let main := (main P_Scomb) in
  wcbvEval (env) 200 (main) = Ret ans_pierce.
  vm_compute. reflexivity.
Qed.
 *)
(** Fibonacci **)
Fixpoint slowFib (n:nat) : nat :=
  match n with
    | 0 => 0
    | S m => match m with
               | 0 => 1
               | S p => slowFib p + slowFib m
             end
  end.
Definition slowFib3 := (slowFib 3).
MetaRocq Quote Recursively Definition cbv_slowFib3 :=
  ltac:(let t:=(eval cbv in slowFib3) in exact t).
Definition ans_slowFib3 :=
 Eval lazy in (test cbv_slowFib3).
(* [program] of the program *)
MetaRocq Quote Recursively Definition p_slowFib3 := slowFib3.
Definition P_slowFib3 := Eval lazy in (test p_slowFib3).
(* Goal
  let env := (env P_slowFib3) in
  let main := (main P_slowFib3) in
  wcbvEval (env) 30 (main) = Ret ans_slowFib3.
  vm_compute. reflexivity.
Qed.
 *)
(* fast Fib *)
Fixpoint fibrec (n:nat) (fs:nat * nat) {struct n} : nat :=
  match n with
    | 0 => fst fs
    | (S n) => fibrec n (pair ((fst fs) + (snd fs)) (fst fs))
  end.
Definition fib : nat -> nat := fun n => fibrec n (pair 0 1).
Definition fib9 := fib 9.
MetaRocq Quote Recursively Definition cbv_fib9 :=
  ltac:(let t:=(eval cbv in fib9) in exact t).
Time Definition ans_fib9 :=
  Eval lazy in (test cbv_fib9).
(* [program] of the program *)
MetaRocq Quote Recursively Definition p_fib9 := fib9.
Definition P_fib9 := Eval lazy in (test p_fib9).
(*
Goal
  let env := (env P_fib9) in
  let main := (main P_fib9) in
  wcbvEval (env) 1000 (main) = Ret ans_fib9.
  vm_compute. reflexivity.
Qed.
 *)

Module HetList.
(** Heterogenous datatypes, a la Matthes **)
Inductive PList : Set->Type:=  (* powerlists *)
| zero : forall A:Set, A -> PList A
| succ : forall A:Set, PList (A * A)%type -> PList A.
Arguments zero {A}.
Arguments succ {A}.
Definition myPList : PList nat :=
  succ (succ (succ (zero (((1,2),(3,4)),((5,6),(7,8)))))).
Unset Asymmetric Patterns.
Fixpoint unzip {A:Set} (l:list (A*A)) {struct l} : list A :=
  match l return list A with
    | nil => nil
    | cons (a1,a2) l' => cons a1 (cons a2 (unzip l'))
  end.
Fixpoint PListToList {A:Set} (l:PList A) {struct l} : list A :=
  match l in PList A return list A with
    | zero a => cons a (nil )
    | succ l' => unzip (PListToList l')
  end.

Time Definition test_myPList := Eval compute in PListToList myPList.

Fixpoint gen_sumPList {A:Set} (l:PList A) {struct l} : (A->nat)->nat :=
  match l in PList A return (A->nat)->nat with
    | zero a => fun f => f a
    | succ l' =>
      fun f => gen_sumPList l' (fun a => let (a1,a2) := a in f a1 + f a2)
  end.
Definition sumPList l := gen_sumPList l (fun x => x).
Definition sumPL_myPL := (sumPList myPList).
MetaRocq Quote Recursively Definition cbv_sumPL_myPL :=
  ltac:(let t:=(eval cbv in sumPL_myPL) in exact t).
Definition ans_sumPL_myPL :=
  Eval lazy in (test cbv_sumPL_myPL).
(* [program] of the program *)
MetaRocq Quote Recursively Definition p_sumPL_myPL := sumPL_myPL.
Definition P_sumPL_myPL := Eval lazy in (test p_sumPL_myPL).
(* Goal
  let env := (env P_sumPL_myPL) in
  let main := (main P_sumPL_myPL) in
  wcbvEval (env) 1000 (main) = Ret ans_sumPL_myPL.
  vm_compute. reflexivity.
Qed.
 *)

Set Implicit Arguments.
Section List.
Variables X Y : Type.
Variable f : X -> Y -> Y.
Fixpoint fold (y : Y) (xs : list X) : Y :=
  match xs with
    | nil => y
    | cons x xr => fold (f x y) xr
  end.
End List.
Inductive Tree := T : list Tree -> Tree.
Fixpoint size (t : Tree) : nat :=
  match t with
    | T ts => S (fold (fun t a => size t + a) 0 ts)
  end.
  Definition unit {A} (a : A) : list A := cons a nil.
  Definition myTree :=
  (T (cons (T (unit (T nil))) (cons (T (unit (T nil))) nil))).


Definition size_myTree := size myTree.
MetaRocq Quote Recursively Definition cbv_size_myTree :=
  ltac:(let t:=(eval cbv in size_myTree) in exact t).
Definition ans_size_myTree :=
  Eval lazy in (test cbv_size_myTree).
(* [program] of the program *)
MetaRocq Quote Recursively Definition p_size_myTree := size_myTree.
Definition P_size_myTree := Eval lazy in (test p_size_myTree).
(* Goal
  let env := (env P_size_myTree) in
  let main := (main P_size_myTree) in
  wcbvEval (env) 100 (main) = Ret ans_size_myTree.
  vm_compute. reflexivity.
Qed.
 *)
End HetList.

From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Peano_dec.
From Stdlib Require Import Arith Init.Wf.
From Stdlib Require Import Program.
Program Fixpoint provedCopy (n:nat) {wf lt n} : nat :=
  match n with 0 => 0 | S k => S (provedCopy k) end.

Print Assumptions provedCopy.
(* MetaRocq Quote Recursively Definition pCopy := provedCopy. program *)

Definition x := 3.
Definition provedCopyx := provedCopy x.
(* Compute provedCopyx.  * evals correctly in Rocq * *)
MetaRocq Quote Recursively Definition cbv_provedCopyx :=
  ltac:(let t:=(eval cbv delta [provedCopyx provedCopy] in provedCopyx) in exact t).
Definition ans_provedCopyx :=
  Eval lazy in (test cbv_provedCopyx).
MetaRocq Quote Recursively Definition p_provedCopyx := provedCopyx. (* program *)
Time Definition P_provedCopyx := Eval lazy in (test cbv_provedCopyx).
(* We don't run this one every time as it is really expensive *)
(*Time Definition P_provedCopyxvm := Eval vm_compute in (test p_provedCopyx).*)

From MetaRocq.ErasurePlugin Require Import Loader.

MetaRocq Erase provedCopyx.
MetaRocq Erase -time -typed -unsafe provedCopyx.

(* From MetaRocq.Erasure.Typed Require Import CertifyingEta.
MetaRocq Run (eta_expand_def
(fun _ => None)
true true
provedCopy). *)

Print P_provedCopyx.

From Stdlib Require Import Streams.

CoFixpoint ones : Stream nat := Cons 1 ones.

MetaRocq Erase ones.
MetaRocq Erase -unsafe ones.

MetaRocq Erase -typed -time -unsafe (map S ones).


(* 0.2s purely in the bytecode VM *)
(*Time Definition P_provedCopyxvm' := Eval vm_compute in (test p_provedCopyx). *)
(* Goal
  let env := (env P_provedCopyx) in
  let main := (main P_provedCopyx) in
  wcbvEval (env) 100 (main) = Ret ans_provedCopyx.
  vm_compute. reflexivity.
Qed.
 *)


 (* debug code in case something is stuck *)
 (*
 From MetaRocq.SafeChecker Require Import PCUICSafeChecker.

Definition fold_matchdecl {A B} (e : EnvCheck A) (b : A -> B) (c : PCUICAst.global_env_ext -> env_error -> B) :=
    match e with
    |CorrectDecl a => b a
    |EnvError g a => c g a
    end.

Ltac fold_matchdecls' := repeat
    match goal with
    |- context C [?x] =>
    match x with
    | match ?l with CorrectDecl a => @?b a | EnvError g a' => @?c g a' end =>
    change x with (fold_matchdecl l b c)
    end
    end.


    Set Printing Depth 20.


Ltac eval_first :=
match goal with
|- context C [fold_matchdecl ?l ?p ?g] =>
  match l with
  (* | fold_matchdecl _ _ _ => fail 1
   *)| _ =>
    idtac "evaluating" l;
    let l' := eval lazy in l in
    let C' := context C [ fold_matchdecl l' p g] in
    convert_concl_no_check C'
  end
end.

Ltac show_match :=
  match goal with
  |- context [match ?x with _ => _ end] =>
    match x with
    | match _ with _ => _ end => fail 1
    | fold_matchdecl _ _ _ => fail 1
    | _ => idtac x
    end
  end.


Goal exists  r, test plusr = r.
Proof.
  eexists.
  unfold  test.
  unfold erase_and_print_template_program.
  unfold erase_template_program.
  unfold bind.
  unfold PCUICSafeChecker.envcheck_monad.
  fold_matchdecls'.
  eval_first.
  show_match.

*)
(* Debuggging

From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure.Typed Require Import ExtractionCorrectness.
From MetaRocq.PCUIC Require Import PCUICAst PCUICProgram.
From MetaRocq.ErasurePlugin Require Import Erasure.
Import Transform.

Program Definition verified_typed_erasure_pipeline
  (cf : checker_flags := extraction_checker_flags)
  {guard : PCUICWfEnvImpl.abstract_guard_impl}
  (efl := EWellformed.all_env_flags) :
  Transform.t _ _
   PCUICAst.term EAst.term _ _
   PCUICTransform.eval_pcuic_program _ :=
   (* a bunch of nonsense for normalization preconditions *)
   let K ty (T : ty -> global_env_ext) p
     := let p := T p in
        (PCUICTyping.wf_ext p -> @PCUICSN.NormalizationIn _ _ p) /\
          (PCUICTyping.wf_ext p -> @PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn _ _ p) in
   let T1 (p:PCUICProgram.global_env_ext_map) := p in
   (* Branches of cases are expanded to bind only variables, constructor types are expanded accordingly *)
   PCUICTransform.pcuic_expand_lets_transform (K _ T1) ▷
   (* Erasure of proofs terms in Prop and types *)
   ETransform.typed_erase_transform ▷
   (* Remove match on box early for dearging *)
   ETransform.remove_match_on_box_typed_transform (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl).

   (* ▷
   (* Check if the preconditions for dearging are valid, otherwise dearging will be the identity *)
   ETransform.dearging_checks_transform (hastrel := eq_refl) (hastbox := eq_refl). *)

#[local] Existing Instance extraction_checker_flags.
Next Obligation. exact extraction_checker_flags. Defined.
Next Obligation. exact extraction_normalizing. Defined.

Next Obligation. exact extraction_checker_flags. Defined.
Next Obligation. exact extraction_normalizing. Defined.
Next Obligation. now split. Qed.

Program Definition pipeline_upto (cf : checker_flags := extraction_checker_flags)
  (guard := fake_guard_impl)
  (efl := EWellformed.all_env_flags) :=
  Transform.compose pre_erasure_pipeline
  verified_typed_erasure_pipeline _.

Program Definition exintro_typed_er p := Transform.Transform.run pipeline_upto p _.
Next Obligation. cbn. todo "assum wt". Qed.

MetaRocq Quote Recursively Definition exintro_proj :=
  (proj1_sig (@exist _ (fun x => x = 0) 0 (@eq_refl _ 0))).

Eval lazy in testty cbv_provedCopyx.

Definition exintro_before_checks := Eval compute in exintro_typed_er exintro_proj.

MetaRocq Quote Recursively Definition quoted_provedCopyx := (provedCopy x).

Definition provedCop_before_checks' := Eval lazy in exintro_typed_er cbv_provedCopyx.

Definition provedCop_before_checks := Eval lazy in exintro_typed_er quoted_provedCopyx.

Import ETransform Optimize.

MetaRocq Typed Erase provedCopyx.
Eval lazy in testty cbv_provedCopyx.
*)
