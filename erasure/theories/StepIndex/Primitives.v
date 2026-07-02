(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv EWellformed EWcbvEval.
From MetaRocq.Utils Require Import bytestring MRString.
From MetaRocq.Erasure Require Import EWcbvEvalCstrsAsBlocksFixLambdaInd.
From MetaRocq.Erasure.StepIndex Require Import Tactics Utils SubstLemmas.
From Stdlib Require Import Relations.Relations.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.
Set Default Proof Using "Type*".

Unset Elimination Schemes.

Inductive eval_primitive_step_index {term term' : Set} (eval : term -> term' -> nat -> Type) :
  prim_val term -> prim_val term' -> nat -> Type :=
  | evalPrimStepIndexInt i : eval_primitive_step_index eval (prim_int i) (prim_int i) 0
  | evalPrimStepIndexFloat f : eval_primitive_step_index eval (prim_float f) (prim_float f) 0
  | evalPrimStepIndexString s : eval_primitive_step_index eval (prim_string s) (prim_string s) 0
  | evalPrimStepIndexArray (v : list term) (def : term) (v' : list term') (def' : term') (ns : list nat) (n : nat) :
      All3 eval v v' ns ->
      eval def def' n ->
      let a := {| array_default := def; array_value := v |} in
      let a' := {| array_default := def'; array_value := v' |} in 
      eval_primitive_step_index eval (prim_array a) (prim_array a') (list_sum ns + n).

Inductive eval_primitive_step_index_ind {term term' : Set} (eval : term → term' → nat → Type) 
  (P : ∀ x y n, eval x y n → Type) : ∀ x y n, eval_primitive_step_index eval x y n → Type :=
| evalPrimStepIndexIntDep i : 
    eval_primitive_step_index_ind eval P (prim_int i) (prim_int i) 0 (evalPrimStepIndexInt eval i)
| evalPrimStepIndexFloatDep f : 
    eval_primitive_step_index_ind eval P (prim_float f) (prim_float f) 0 (evalPrimStepIndexFloat eval f)
| evalPrimStepIndexStringDep s : 
    eval_primitive_step_index_ind eval P (prim_string s) (prim_string s) 0 (evalPrimStepIndexString eval s)
| evalPrimStepIndexArrayDep v def v' def' ns n (ev : All3 eval v v' ns) (ed : eval def def' n) : 
    All3_over ev P → 
    P def def' n ed → 
    let a := {| array_default := def; array_value := v |} in
    let a' := {| array_default := def'; array_value := v' |} in
    eval_primitive_step_index_ind eval P (prim_array a) (prim_array a') _ (evalPrimStepIndexArray eval v def v' def' ns n ev ed)
.
Set Elimination Schemes.


Definition map_eval_primitive_step_index {term term' : Set} {eval : term -> term' -> nat -> Type} 
  {P : ∀ x y c, eval x y c -> Type} (h : ∀ x y c e, P x y c e) {p p' c} ev : eval_primitive_step_index_ind eval P p p' c ev := 
  match ev with
  | evalPrimStepIndexInt i => evalPrimStepIndexIntDep eval P i
  | evalPrimStepIndexFloat f => evalPrimStepIndexFloatDep eval P f
  | evalPrimStepIndexString s => evalPrimStepIndexStringDep eval P s
  | evalPrimStepIndexArray  v def v' def' ns n ev ed => 
      evalPrimStepIndexArrayDep _ _ _ _ _ _ _ _ _ _ (map_All3_dep _ h ev) (h _ _ _ ed)
  end.