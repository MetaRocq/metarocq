From Stdlib Require Import PArith Sint63 String Uint63 PrimFloat SpecFloat FloatOps PString.
From MetaRocq.Utils Require Import bytestring MRString.

(* Circumventing https://github.com/coq/coq/issues/19150 (via PString). *)
Ltac Zify.zify_post_hook ::= idtac.

Local Open Scope bs_scope.

Class Show (A : Type) := show : A -> string.
Global Hint Mode Show ! : typeclass_instances.

#[export] Instance show_bytestring : Show string := fun x => x.

#[export] Instance show_string : Show String.string := bytestring.String.of_string.

Definition string_show {A} {show : Show A} : A -> String.string :=
  fun a => bytestring.String.to_string (show a).

#[export] Instance nat_show : Show nat := string_of_nat.

Definition string_of_bool b := if (b : bool) then "true" else "false".

#[export] Instance show_bool : Show bool := string_of_bool.
#[export] Instance show_pair {A B} {showA : Show A} {showB : Show B}: Show (A * B) :=
  { show '(x, y) := "(" ++ show x ++ ", " ++ show y ++ ")" }.

#[export] Instance show_sum {A B} {showA : Show A} {showB : Show B}: Show (A + B) :=
  { show x := match x with
    | inl x => "(inl " ++ show x ++ ")"
    | inr x => "(inr " ++ show x ++ ")"
    end
    }.

Definition string_of_option {A} (fn : A -> string) (x : option A) : string :=
  match x with
  | None => "None"
  | Some x => "(Some " ++ fn x ++ ")"
  end.

#[export] Instance show_option {A} {showA : Show A}: Show (option A) := string_of_option show.

#[export] Instance show_list {A} {SA : Show A} : Show (list A) := string_of_list show.

Import SpecFloat.
Definition string_of_specfloat (f : SpecFloat.spec_float) :=
  match f with
  | S754_zero sign => if sign then "-0" else "0"
  | S754_infinity sign => if sign then "-infinity" else "infinity"
  | S754_nan => "nan"
  | S754_finite sign p z =>
  let num := string_of_positive p ++ "p" ++ string_of_Z z in
  if sign then "-" ++ num else num
  end.

Definition string_of_prim_int (i:Uint63.int) : string :=
  (* Better? DecimalString.NilZero.string_of_uint (BinNat.N.to_uint (BinInt.Z.to_N (Int63.to_Z i))). ? *)
  string_of_Z (Uint63.to_Z i).

Definition string_of_float (f : PrimFloat.float) : string :=
  string_of_specfloat (FloatOps.Prim2SF f).

Definition char63_to_string (c : PrimString.char63) : string :=
  let b :=
    match Byte.of_N (BinInt.Z.to_N (Uint63.to_Z c)) with
    | None => Byte.x00
    | Some b => b
    end
  in
  String.String b String.EmptyString.

Definition string_of_pstring (s : PrimString.string) : string :=
  string_of_list char63_to_string (PrimStringAxioms.to_list s).

#[export] Instance show_uint : Show PrimInt63.int := string_of_prim_int.
#[export] Instance show_sint : Show int_wrapper := { show x := string_of_Z (Sint63.to_Z (x.(int_wrap))) }.
#[export] Instance show_specfloat : Show SpecFloat.spec_float := string_of_specfloat.
#[export] Instance show_float : Show PrimFloat.float := string_of_float.
#[export] Instance show_positive : Show positive := string_of_positive.
#[export] Instance show_Z : Show Z := string_of_Z.
#[export] Instance show_pstring : Show PrimString.string := string_of_pstring.
