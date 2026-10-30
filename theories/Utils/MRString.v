From Stdlib Require Import ssreflect ssrbool Decimal DecimalString ZArith.
From MetaRocq.Utils Require Import MRCompare bytestring ReflectEq.

Local Open Scope bs.
Abbreviation string := String.t.

(** When defining [Show] instance for your own datatypes, you sometimes need to
    start a new line for better printing. [nl] is a shorthand for it. *)
Definition nl : string := String.String "010"%byte String.EmptyString.

Definition string_of_list_aux {A} (f : A -> string) (sep : string) (l : list A) : string :=
  let fix aux l :=
      match l return string with
      | nil => ""
      | cons a nil => f a
      | cons a l => f a ++ sep ++ aux l
      end
  in aux l.

Definition string_of_list {A} (f : A -> string) (l : list A) : string :=
  "[" ++ string_of_list_aux f "," l ++ "]".

Definition print_list {A} (f : A -> string) (sep : string) (l : list A) : string :=
  string_of_list_aux f sep l.

Definition parens (top : bool) (s : string) :=
  if top then s else "(" ++ s ++ ")".

Local Infix "::" := String.String.

Fixpoint string_of_uint n :=
  match n with
  | Nil => ""
  | D0 n => "0" :: string_of_uint n
  | D1 n => "1" :: string_of_uint n
  | D2 n => "2" :: string_of_uint n
  | D3 n => "3" :: string_of_uint n
  | D4 n => "4" :: string_of_uint n
  | D5 n => "5" :: string_of_uint n
  | D6 n => "6" :: string_of_uint n
  | D7 n => "7" :: string_of_uint n
  | D8 n => "8" :: string_of_uint n
  | D9 n => "9" :: string_of_uint n
  end.

Definition string_of_nat n : string :=
  string_of_uint (Nat.to_uint n).

#[global]
Hint Resolve String.string_dec : eq_dec.

Definition string_of_positive p :=
  string_of_uint (Pos.to_uint p).

Definition string_of_Z (z : Z) : string :=
  match z with
  | Z0 => "0"
  | Zpos p => string_of_positive p
  | Zneg p => "-" ++ string_of_positive p
  end.
