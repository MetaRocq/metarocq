From Ltac2 Require Import Ltac2.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import NArith.
From MetaRocq.Utils Require Import monad_utils.
From MetaRocq.Template Require Import Loader TemplateMonad.Core.

Local Set Default Proof Mode "Classic".

Definition six := tmFix (fun f a => if (6 <? a) then ret 6 else f (S a))%nat 0%nat.
Goal True.
  run_template_program six (fun v => constr_eq v 6%nat).
Abort.

(* Let's compare some timing numbers *)
Module TCMonomorphic.
  Import MRMonadNotation.
  Import bytestring.
  Local Unset Universe Polymorphism.
  (* We use monomorphic universes for performance *)
  Monomorphic Universes fixa fixb fixt fixu.
  Monomorphic Class HasFix := tmFix_ : forall {A : Type@{fixa}} {B : Type@{fixb}} (f : (A -> TemplateMonad@{fixt fixu} B) -> (A -> TemplateMonad@{fixt fixu} B)), A -> TemplateMonad@{fixt fixu} B.
  (* idk why this is needed... *)
  #[local] Hint Extern 1 (Monad _) => refine TemplateMonad_Monad : typeclass_instances.
  Monomorphic Definition tmFix {A : Type@{fixa}} {B : Type@{fixb}} (f : (A -> TemplateMonad@{fixt fixu} B) -> (A -> TemplateMonad@{fixt fixu} B)) : A -> TemplateMonad@{fixt fixu} B
    := f
         (fun a
          => tmFix <- tmInferInstance None HasFix;;
             match tmFix with
             | Common.my_Some tmFix => tmFix _ _ f a
             | Common.my_None => tmFail "Internal Error: No tmFix instance"%bs
             end).
  #[global] Hint Extern 0 HasFix => refine @tmFix : typeclass_instances.
  Definition six := tmFix (fun f a => if (6 <? a) then ret 6 else f (S a))%nat 0%nat.
  Goal True.
    run_template_program six (fun v => constr_eq v 6%nat).
  Abort.
End TCMonomorphic.
Module TC.
  Local Set Universe Polymorphism.
  Local Unset Universe Minimization ToSet.
  (** This is a kludge, it would be nice to do better *)
  Class HasFix : Prop := tmFix_ : forall {A B} (f : (A -> TemplateMonad B) -> (A -> TemplateMonad B)), A -> TemplateMonad B.
  (* idk why this is needed... *)
  #[local] Hint Extern 1 (Monad _) => refine TemplateMonad_Monad : typeclass_instances.
  Import MRMonadNotation.
  Import bytestring.
  Local Unset Universe Checking.
  Definition tmFix {A B} (f : (A -> TemplateMonad B) -> (A -> TemplateMonad B)) : A -> TemplateMonad B
    := f
         (fun a
          => tmFix <- tmInferInstance None HasFix;;
             match tmFix return TemplateMonad B with
             | Common.my_Some tmFix => tmFix _ _ f a
             | Common.my_None => tmFail "Internal Error: No tmFix instance"%bs
             end).
  #[global] Hint Extern 0 HasFix => refine @tmFix : typeclass_instances.
  Definition six := tmFix (fun f a => if (6 <? a) then ret 6 else f (S a))%nat 0%nat.
  Goal True.
    run_template_program six (fun v => constr_eq v 6%nat).
  Abort.
End TC.
Module Unquote.
  Import MRMonadNotation.
  Import MetaRocq.Common.Universes.
  Import MetaRocq.Template.Ast.
  Import bytestring.
  Import ListNotations.
  Local Set Universe Polymorphism.
  Local Unset Universe Minimization ToSet.
  (* idk why this is needed... *)
  #[local] Hint Extern 1 (Monad _) => refine TemplateMonad_Monad : typeclass_instances.
  Definition tmQuoteSort@{U t u} : TemplateMonad@{t u} sort
    := bind@{t u} (@tmQuote@{t u} Prop (Type@{U} -> True)) (fun p =>
      match p with
      | tProd _ (tSort s) _ => ret@{t u} s
      | _ => tmFail "Anomaly: tmQuote (Type -> True) should be (tProd _ (tSort _) _)!"%bs
      end).
  Definition tmQuoteUniverse@{U t u} : TemplateMonad@{t u} Universe.t
    := bind@{t u} (@tmQuoteSort@{U t u}) (fun s =>
      match s with
      | sType u => ret u
      | _ => tmFail "Sort does not carry a universe (is not Type)"%bs
      end).
  Definition tmQuoteLevel@{U t u} : TemplateMonad@{t u} Level.t
    := bind@{t u} tmQuoteUniverse@{U t u}
       (fun u =>
       match Universe.get_is_level u with
       | Some l => ret l
       | None => tmFail "Universe is not a level"%bs
       end).
  Definition self := ltac:(run_template_program (tmCurrentModPath tt) (fun v => exact v)).
  (* (* this one is 5x slower *)
  Definition tmFix@{a b t u} {A : Type@{a}} {B : Type@{b}} (f : (A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) : A -> TemplateMonad@{t u} B
    := f (fun a
          => (qA <- tmQuote A;;
              qB <- tmQuote B;;
              qa <- tmQuoteLevel@{a _ _};;
              qb <- tmQuoteLevel@{b _ _};;
              qt <- tmQuoteLevel@{t _ _};;
              qu <- tmQuoteLevel@{u _ _};;
              let self := tConst (self, "tmFix"%bs) [qa;qb;qt;qu] in
              tmFix <- tmUnquoteTyped (((A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) -> A -> TemplateMonad@{t u} B) (mkApps self [qA; qB]);;
              tmFix f a)).
   *)
  Definition tmFix'@{a b t u} {A : Type@{a}} {B : Type@{b}} (qtmFix' : Ast.term) (f : (A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) : A -> TemplateMonad@{t u} B
    := f (fun a
          => bind@{t u} (tmUnquoteTyped (Ast.term -> ((A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) -> A -> TemplateMonad@{t u} B) qtmFix')
             (fun tmFix => tmFix qtmFix' f a)).
  Definition tmFix@{a b t u} {A : Type@{a}} {B : Type@{b}} (f : (A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) : A -> TemplateMonad@{t u} B
    := f (fun a
          => (bind@{t u} (tmQuote@{t u} A) (fun qA =>
              bind@{t u} (tmQuote@{t u} B) (fun qB =>
              bind@{t u} tmQuoteUniverse@{a t u} (fun qa =>
              bind@{t u} tmQuoteUniverse@{b t u} (fun qb =>
              bind@{t u} tmQuoteUniverse@{t t u} (fun qt =>
              bind@{t u} tmQuoteUniverse@{u t u} (fun qu =>
              let self := tConst (self, "tmFix'"%bs) [qa;qb;qt;qu] in
              @tmFix'@{a b t u} A B (mkApps self [qA; qB]) f a)))))))).
  (* reference that uses the constant in Core, for equality comparison *)
  Definition tmFix_ref@{a b t u} {A : Type@{a}} {B : Type@{b}} (f : (A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) : A -> TemplateMonad@{t u} B
    := f (fun a =>
            bind@{t u} (tmQuote@{t u} A) (fun qA =>
            bind@{t u} (tmQuote@{t u} B) (fun qB =>
            bind@{t u} tmQuoteUniverse@{a t u} (fun qa =>
            bind@{t u} tmQuoteUniverse@{b t u} (fun qb =>
            bind@{t u} tmQuoteUniverse@{t t u} (fun qt =>
            bind@{t u} tmQuoteUniverse@{u t u} (fun qu =>
            let self := tConst (MPfile ["Core"; "TemplateMonad"; "Template"; "MetaRocq"], "tmFix'")%bs [qa;qb;qt;qu] in
            @tmFix'@{a b t u} A B (mkApps self [qA; qB]) f a))))))).
  Definition six := tmFix (fun f a => if (6 <? a) then ret 6 else f (S a))%nat 0%nat.
  Goal True.
    run_template_program six (fun v => constr_eq v 6%nat).
  Abort.
End Unquote.
Module NoGuard.
  (* N.B. This version is inconsistent *)
  Import MRMonadNotation.
  Import MetaRocq.Common.Universes.
  Import MetaRocq.Template.Ast.
  Import bytestring.
  Import ListNotations.
  Local Set Universe Polymorphism.
  Local Unset Universe Minimization ToSet.
  (* idk why this is needed... *)
  #[local] Hint Extern 1 (Monad _) => refine TemplateMonad_Monad : typeclass_instances.
  Local Unset Guard Checking. (* Inconsistent!  See https://coq.zulipchat.com/#narrow/stream/237658-MetaRocq/topic/.60tmFix.60point.20combinator/near/311488798 *)
  Definition tmFix {A B} (f : (A -> TemplateMonad B) -> (A -> TemplateMonad B)) : A -> TemplateMonad B
    := (fix tmFix (dummy : unit) {struct dummy} : A -> @TemplateMonad B
        := f (fun a => tmFix tt a)) tt.
  Local Set Guard Checking.
  Definition six := tmFix (fun f a => if (6 <? a) then ret 6 else f (S a))%nat 0%nat.
  Goal True.
    run_template_program six (fun v => constr_eq v 6%nat).
  Abort.
End NoGuard.
Definition count_down_MR
  := tmFix (fun f x => let x := N.pred x in
                       match x with
                       | 0 => ret 0
                       | _ => f x
                       end%N).
Definition count_down_MR_tc
  := TC.tmFix (fun f x => let x := N.pred x in
                          match x with
                          | 0 => ret 0
                          | _ => f x
                          end%N).
Definition count_down_MR_tc_monomorphic
  := TCMonomorphic.tmFix (fun f x => let x := N.pred x in
                                     match x with
                                     | 0 => ret 0
                                     | _ => f x
                                     end%N).
Definition count_down_MR_unquote
  := Unquote.tmFix (fun f x => let x := N.pred x in
                               match x with
                               | 0 => ret 0
                               | _ => f x
                               end%N).
(* reference that uses the constant in Core, for equality comparison *)
Definition count_down_MR_unquote_ref
  := Unquote.tmFix_ref (fun f x => let x := N.pred x in
                                   match x with
                                   | 0 => ret 0
                                   | _ => f x
                                   end%N).
Definition count_down_MR_noguard
  := NoGuard.tmFix (fun f x => let x := N.pred x in
                       match x with
                       | 0 => ret 0
                       | _ => f x
                       end%N).
Definition count_down_wf (v : N) : N.
Proof.
  refine (Fix (Acc_intro_generator (N.to_nat (2 * (1 + N.log2_up v))) N.lt_wf_0)
            (fun _ => N)
            (fun x rec => let x := N.pred x in
                          match x as y return x = y -> _ with
                          | 0 => fun _ => 0
                          | _ => fun pf => rec x _
                          end%N eq_refl)
            v).
  abstract lia.
Defined.
Module NoGuardFix.
  Local Unset Guard Checking. (* Inconsistent! *)
  Definition Fix {A B} (f : (A -> B) -> (A -> B)) : A -> B
    := (fix Fix (dummy : unit) {struct dummy} : A -> B
        := f (fun a => Fix tt a)) tt.
  Local Set Guard Checking.
End NoGuardFix.
Definition count_down_noguard (v : N) : N
  := NoGuardFix.Fix
       (fun rec x => let x := N.pred x in
                     match x with
                     | 0 => 0
                     | _ => rec x
                     end%N)
       v.
Ltac count_down v :=
  lazymatch (eval vm_compute in (N.pred v)) with
  | 0%N => constr:(0%N)
  | ?v => count_down v
  end.

(** We replace notations taking constr with tactic, so that we don't
    pay the cost of retyping, see
    COQBUG(https://github.com/coq/coq/issues/16586) *)
Ltac2 Notation "eval" "cbv" s(strategy) "in" c(tactic(6)) := Std.eval_cbv s c.
Ltac2 Notation "eval" "lazy" s(strategy) "in" c(tactic(6)) := Std.eval_lazy s c.
Ltac2 Notation "eval" "vm_compute" pl(opt(seq(pattern, occurrences))) "in" c(tactic(6)) := Std.eval_vm pl c.
Ltac2 Notation "eval" "native_compute" pl(opt(seq(pattern, occurrences))) "in" c(tactic(6)) := Std.eval_native pl c.

Ltac2 count_down v :=
  let pred := 'N.pred in
  let arr := Array.make 1 pred in
  let z := '0%N in
  let mkPred v := (Array.set arr 0 v;
                   Constr.Unsafe.make (Constr.Unsafe.App pred arr)) in
  let rec count_down v :=
    let v := (eval vm_compute in (mkPred v)) in
    if Constr.equal v z
    then z
    else count_down v in
  count_down v.

(* Make sure that we're using the unquote-based fix *)
Check eq_refl : @tmFix = @Unquote.tmFix_ref.
Check eq_refl : @count_down_MR = @count_down_MR_unquote_ref.

(* --- *)

Definition bignum := (2^20)%N.
Definition smallnum := (2^15)%N.
Definition extremelysmallnum := (2^8)%N.

(* This is pretty slow :-( *)
Time Check ltac:(run_template_program (count_down_MR_tc extremelysmallnum) (fun v => exact v)). (* 5.378 secs (5.378u,0.s) *)
(* universes are apparently a bottleneck *)
Time Check ltac:(run_template_program (count_down_MR_tc_monomorphic extremelysmallnum) (fun v => exact v)). (* 0.093 secs (0.093u,0.s) *)
Time Check ltac:(run_template_program (count_down_MR_unquote extremelysmallnum) (fun v => exact v)). (* 0.093 secs (0.093u,0.s) *)
Time Check ltac:(run_template_program (count_down_MR_noguard extremelysmallnum) (fun v => exact v)). (* 0.001 secs (0.001u,0.s) *)
(* test the actually used one *)
Time Check ltac:(run_template_program (count_down_MR extremelysmallnum) (fun v => exact v)).
(* now we use bigger numbers *)
Time Check ltac:(run_template_program (count_down_MR_tc_monomorphic smallnum) (fun v => exact v)). (* 7.64 secs (7.64u,0.s) *)
(* unquote is a bit slower here *)
Time Check ltac:(run_template_program (count_down_MR_unquote smallnum) (fun v => exact v)). (* 10.874 secs (10.874u,0.s) *)
Time Check ltac:(run_template_program (count_down_MR_noguard smallnum) (fun v => exact v)). (* 0.115 secs (0.115u,0.s) *)
Time Check ltac:(run_template_program (count_down_MR smallnum) (fun v => exact v)).
Time Eval lazy in count_down_wf smallnum. (* 0.305 secs (0.305u,0.s) *)
Time Eval cbv in count_down_wf smallnum. (* 0.328 secs (0.328u,0.s) *)
Time Eval lazy in count_down_noguard smallnum. (* 0.138 secs (0.138u,0.s) *)
Time Eval cbv in count_down_noguard smallnum. (* 0.15 secs (0.15u,0.s) *)
Time Check ltac:(let v := count_down smallnum in exact v). (* 4.612 secs (4.612u,0.s) *)
Time Check ltac2:(let v := count_down 'smallnum in exact $v). (* 2.404 secs (2.404u,0.s) *)
(* and now we can use even bigger numbers *)
Time Eval native_compute in count_down_wf bignum. (* 1.133 secs (0.863u,0.s) *)
Time Eval vm_compute in count_down_wf bignum. (* 0.432 secs (0.432u,0.s) *)
Time Eval native_compute in count_down_noguard bignum. (* 0.336 secs (0.048u,0.s) *)
Time Eval vm_compute in count_down_noguard bignum. (* 0.178 secs (0.178u,0.s) *)
