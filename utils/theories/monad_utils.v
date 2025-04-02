Require Import Arith List.
From MetaCoq.Utils Require Import All_Forall MCSquash.
From Equations Require Import Equations.
Coercion is_true : bool >-> Sortclass.

Import ListNotations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
{ ret : forall {t : Type@{d}}, t -> m t
; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
}.
Global Arguments Build_Monad _ & _ _. (* for better type inference and error messages *)

Class MonadExc E (m : Type -> Type) : Type :=
{ raise : forall {T}, E -> m T
; catch : forall {T}, m T -> (E -> m T) -> m T
}.
Global Arguments Build_MonadExc _ _ & _ _. (* for better type inference and error messages *)


Module MCMonadNotation.
  Declare Scope monad_scope.
  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 50, left associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 51, right associativity) : monad_scope.

  Notation "'mlet' x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity, x pattern) : monad_scope.

  Notation "'mlet' ' pat <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

  Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

  Notation "' pat <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 100, right associativity) : monad_scope.
End MCMonadNotation.

Import MCMonadNotation.

#[global] Instance option_monad : Monad option :=
  {| ret A a := Some a ;
     bind A B m f :=
       match m with
       | Some a => f a
       | None => None
       end
  |}.

#[global] Instance id_monad : Monad (fun x => x) :=
  {| ret A a := a ;
     bind A B m f := f m
  |}.

#[global] Instance option_monad_exc : MonadExc unit option :=
{| raise T _ := None ;
    catch T m f :=
      match m with
      | Some a => Some a
      | None => f tt
      end
|}.

Open Scope monad.

(* state is underneath the other monad *)
Definition StateT S M T := S -> M (T * S)%type.
Definition StateT_Monad {S T} {TM : Monad T} : Monad (StateT S T) :=
  {| ret A a st := ret (a, st) ;
     bind A B m f st := '(m, st) <- m st;; f m st
  |}.
#[export] Hint Extern 1 (Monad (StateT ?S ?T)) => simple apply (@StateT_Monad S T) : typeclass_instances.

Module State.
  Definition get {S T} {TM : Monad T} : StateT S T S
    := fun s => ret (s, s).
  Definition update {S T} {TM : Monad T} (f : S -> S) : StateT S T unit
    := fun s => ret (tt, f s).
  Definition set {S T} {TM : Monad T} (s : S) : StateT S T unit
    := update (fun _ => s).
  Definition lift {S T} {TM : Monad T} {A} (m : T A) : StateT S T A
    := fun s => v <- m;; ret (v, s).
  Definition evalStateT {S T A} {TM : Monad T} (p : StateT S T A) (st : S) : T A
    := '(v, st) <- p st;;
       ret v.
End State.

Section MapOpt.
  Context {A} {B} (f : A -> option B).

  Fixpoint mapopt (l : list A) : option (list B) :=
    match l with
    | nil => ret nil
    | x :: xs => x' <- f x ;;
                xs' <- mapopt xs ;;
                ret (x' :: xs')
    end.
End MapOpt.

Section MonadOperations.
  Context {T : Type -> Type} {M : Monad T}.
  Context {A B} (f : A -> T B).
  Fixpoint monad_map (l : list A)
    : T (list B)
    := match l with
       | nil => ret nil
       | x :: l => x' <- f x ;;
                  l' <- monad_map l ;;
                  ret (x' :: l')
       end.

  Definition monad_option_map (l : option A)
    : T (option B)
    := match l with
       | None => ret None
       | Some x => x' <- f x ;;
                   ret (Some x')
       end.

  Context (g : A -> B -> T A).
  Fixpoint monad_fold_left (l : list B) (x : A) : T A
    := match l with
       | nil => ret x
       | y :: l => x' <- g x y ;;
                   monad_fold_left l x'
       end.

  Fixpoint monad_fold_right (l : list B) (x : A) : T A
       := match l with
          | nil => ret x
          | y :: l => l' <- monad_fold_right l x ;;
                      g l' y
          end.

  Context (h : nat -> A -> T B).
  Fixpoint monad_map_i_aux (n0 : nat) (l : list A) : T (list B)
    := match l with
       | nil => ret nil
       | x :: l => x' <- (h n0 x) ;;
                   l' <- (monad_map_i_aux (S n0) l) ;;
                   ret (x' :: l')
       end.

  Definition monad_map_i := @monad_map_i_aux 0.
End MonadOperations.

Section MonadOperations.
  Context {T} {M : Monad T} {E} {ME : MonadExc E T}.
  Context {A B C} (f : A -> B -> T C) (e : E).
  Fixpoint monad_map2 (l : list A) (l' : list B) : T (list C) :=
    match l, l' with
    | nil, nil => ret nil
    | x :: l, y :: l' =>
      x' <- f x y ;;
      xs' <- monad_map2 l l' ;;
      ret (x' :: xs')
    | _, _ => raise e
    end.
End MonadOperations.

Definition monad_iter {T : Type -> Type} {M A} (f : A -> T unit) (l : list A) : T unit
  := @monad_fold_left T M _ _ (fun _ => f) l tt.

Fixpoint monad_All {T : Type -> Type} {M : Monad T} {A} {P} (f : forall x, T (P x)) l : T (@All A P l) := match l with
   | [] => ret All_nil
   | a :: l => X <- f a ;;
              Y <- monad_All f l ;;
              ret (All_cons X Y)
   end.

Fixpoint monad_All2 {T : Type -> Type} {E} {M : Monad T} {M' : MonadExc E T} wrong_sizes
  {A B R} (f : forall x y, T (R x y)) l1 l2 : T (@All2 A B R l1 l2) :=
  match l1, l2 with
   | [], [] => ret All2_nil
   | a :: l1, b :: l2 => X <- f a b ;;
                        Y <- monad_All2 wrong_sizes f l1 l2 ;;
                        ret (All2_cons X Y)
   | _, _ => raise wrong_sizes
   end.

Definition monad_prod {T} {M : Monad T} {A B} (x : T A) (y : T B): T (A * B)%type
  := X <- x ;; Y <- y ;; ret (X, Y).

(** monadic checks *)
Definition check_dec {T : Type -> Type} {E : Type} {M : Monad T} {M' : MonadExc E T} (e : E) {P}
  (H : {P} + {~ P}) : T P
  := match H with
  | left x => ret x
  | right _ => raise e
  end.

Definition check_eq_true {T : Type -> Type} {E : Type} {M : Monad T} {M' : MonadExc E T} (b : bool) (e : E) : T b :=
  if b return T b then ret eq_refl else raise e.

Definition check_eq_nat {T : Type -> Type} {E : Type} {M : Monad T} {M' : MonadExc E T} n m (e : E) : T (n = m) :=
  match PeanoNat.Nat.eq_dec n m with
  | left p => ret p
  | right p => raise e
  end.

Program Fixpoint monad_Alli {T : Type -> Type} {M : Monad T} {A} {P} (f : forall n x, T (∥ P n x ∥)) l n
  : T (∥ @Alli A P n l ∥)
  := match l with
      | [] => ret (sq Alli_nil)
      | a :: l => X <- f n a ;;
                  Y <- monad_Alli f l (S n) ;;
                  ret _
      end.
Next Obligation.
  sq. constructor; assumption.
Defined.

Program Fixpoint monad_Alli_All {T : Type -> Type} {M : Monad T} {A} {P} {Q} (f : forall n x, ∥ Q x ∥ -> T (∥ P n x ∥)) l n :
  ∥ All Q l ∥ -> T (∥ @Alli A P n l ∥)
  := match l with
      | [] => fun _ => ret (sq Alli_nil)
      | a :: l => fun allq => X <- f n a _ ;;
                  Y <- monad_Alli_All f l (S n) _ ;;
                  ret _
      end.
Next Obligation. sq.
  now depelim allq.
Qed.
Next Obligation.
  sq; now depelim allq.
Qed.
Next Obligation.
  sq. constructor; assumption.
Defined.

Section monad_Alli_nth.
  Context {T} {M : Monad T} {A} {P : nat -> A -> Type}.
  Program Fixpoint monad_Alli_nth_gen l k
    (f : forall n x, nth_error l n = Some x -> T (∥ P (k + n) x ∥)) :
    T (∥ @Alli A P k l ∥)
    := match l with
      | [] => ret (sq Alli_nil)
      | a :: l => X <- f 0 a _ ;;
                  Y <- monad_Alli_nth_gen l (S k) (fun n x hnth => px <- f (S n) x hnth;; ret _) ;;
                  ret _
      end.
    Next Obligation.
      sq. now rewrite Nat.add_succ_r in px.
    Qed.
    Next Obligation.
      sq. rewrite Nat.add_0_r in X. constructor; auto.
    Qed.

  Definition monad_Alli_nth l (f : forall n x, nth_error l n = Some x -> T (∥ P n x ∥)) : T (∥ @Alli A P 0 l ∥) :=
    monad_Alli_nth_gen l 0 f.

End monad_Alli_nth.

Section MonadAllAll.
  Context {T : Type -> Type} {M : Monad T} {A} {P : A -> Type} {Q} (f : forall x, ∥ Q x ∥ -> T (∥ P x ∥)).
  Program Fixpoint monad_All_All l : ∥ All Q l ∥ -> T (∥ All P l ∥) :=
    match l return ∥ All Q l ∥ -> T (∥ All P l ∥) with
      | [] => fun _ => ret (sq All_nil)
      | a :: l => fun allq =>
      X <- f a _ ;;
      Y <- monad_All_All l _ ;;
      ret _
      end.
  Next Obligation. sq.
    now depelim allq.
  Qed.
  Next Obligation.
    sq; now depelim allq.
  Qed.
  Next Obligation.
    sq. constructor; assumption.
  Defined.
End MonadAllAll.
