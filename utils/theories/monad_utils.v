From Stdlib Require Import Arith List.
From MetaRocq.Utils Require Import All_Forall MRSquash.
From Equations Require Import Equations.
From ExtLib Require Export Monads.
From ExtLib Require Export OptionMonad.

Coercion is_true : bool >-> Sortclass.

Import MonadNotation.
Import ListNotations.

Set Universe Polymorphism.



#[global] Instance id_monad : Monad (fun x => x) :=
  {| ret A a := a ;
     bind A B m f := f m
  |}.


Open Scope monad.

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
