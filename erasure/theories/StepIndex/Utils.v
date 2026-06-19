(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv EWellformed EWcbvEval.
From MetaRocq.Erasure.StepIndex Require Import Tactics.
From MetaRocq.Utils Require Import bytestring MRString.
From Stdlib Require Import ssreflect ssrbool.
Set Default Proof Using "Type*".


Definition cunfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match nth_error mfix idx with
  | Some ({| dbody := tLambda _ d |}) => Some d
  | _ => None
  end.


Fixpoint All3_over {A B C : Type} {P : A -> B -> C -> Type} {la : list A} {lb : list B} {lc : list C}
  (a : All3 P la lb lc) (g : ∀ x y z, P x y z -> Type) : Type :=
  match a with
  | All3_nil => ()
  | All3_cons _ _ _ _ _ _ h t => (g _ _ _ h)  * All3_over t g 
  end.


Fixpoint map_All3_dep {A B C : Type} (P : A -> B -> C -> Type) {hP : ∀ a b c, P a b c -> Type} 
  (h: ∀ a b c e, hP a b c e) {la : list A} {lb : list B} {lc : list C}
  (ev : All3 P la lb lc) : All3_over ev hP :=
    match ev return All3_over ev hP with
    | All3_nil => tt
    | All3_cons _ _ _ _ _ _ Pabc ev => (h _ _ _ Pabc, map_All3_dep P h ev)
    end.


(* TODO: See to change the original def which forces X = term *)
Definition has_prim {X} {epfl : EPrimitiveFlags} (p : prim_val X) :=
  match p.π1 with
  | Primitive.primInt => has_primint
  | Primitive.primFloat => has_primfloat
  | Primitive.primString => has_primstring
  | Primitive.primArray => has_primarray
  end.


Lemma size_rev {A : Type} (l : list A) :
  #|List.rev l| = #|l|.
Proof.
  induction l as [|? ? IH]; now simple.
Qed.
Hint Rewrite @size_rev : rw_hints.


Lemma fold_left_map_def {A B : Set} (f : A -> B -> A) env (d : def A) : 
  fold_left (λ b d, map_def (λ t, f t d) b) env d = map_def (λ b, fold_left f env b) d.
Proof.
  unfold map_def; induction env in d |- *; destruct d; simpl; easy.
Qed.


Lemma Forall_same_In {A} (P : A -> A -> Prop) l :
  Forall2 P l l <-> ∀ x, In x l -> P x x.
Proof.
  induction l as [|a l IH]; split; simpl; try easy.
  - intros h x [->| hIn]; inversion h; subst; now simpl.
  - intros h; constructor; simpl; try easy.
    now apply IH.
Qed.
Hint Rewrite @Forall_same_In : rw_hints.


Lemma fix_subst_map l : fix_subst l = map (tFix l) (List.rev (seq 0 #|l|)).
Proof.
  unfold fix_subst.
  generalize #|l| as n.
  induction n; first reflexivity.
  now rewrite IHn seq_S rev_app_distr.
Qed.