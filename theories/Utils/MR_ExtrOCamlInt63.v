(************************************************************************)
(*         *   The Rocq Proof Assistant / The Rocq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction to OCaml of native 63-bit machine integers. *)

From Stdlib Require Uint63 Sint63 Extraction.

(** Basic data types used by some primitive operators. *)

Extract Inductive bool => bool [ true false ].
Extract Inductive prod => "( * )" [ "" ].
Extract Inductive DoubleType.carry => "MRUint63.carry" [ "MRUint63.C0" "MRUint63.C1" ].

(** Primitive types and operators. *)
Extract Constant Uint63.int => "MRUint63.t".
Extraction Inline Uint63.int.
(* Otherwise, the name conflicts with the primitive OCaml type [int] *)

Extract Constant Uint63.lsl => "MRUint63.l_sl".
Extract Constant Uint63.lsr => "MRUint63.l_sr".
Extract Constant Sint63.asr => "MRUint63.a_sr".
Extract Constant Uint63.land => "MRUint63.l_and".
Extract Constant Uint63.lor => "MRUint63.l_or".
Extract Constant Uint63.lxor => "MRUint63.l_xor".

Extract Constant Uint63.add => "MRUint63.add".
Extract Constant Uint63.sub => "MRUint63.sub".
Extract Constant Uint63.mul => "MRUint63.mul".
Extract Constant Uint63.mulc => "MRUint63.mulc".
Extract Constant Uint63.div => "MRUint63.div".
Extract Constant Uint63.mod => "MRUint63.rem".
Extract Constant Sint63.div => "MRUint63.divs".
Extract Constant Sint63.rem => "MRUint63.rems".


Extract Constant Uint63.eqb => "MRUint63.equal".
Extract Constant Uint63.ltb => "MRUint63.lt".
Extract Constant Uint63.leb => "MRUint63.le".
Extract Constant Sint63.ltb => "MRUint63.lts".
Extract Constant Sint63.leb => "MRUint63.les".

Extract Constant Uint63.addc => "MRUint63.addc".
Extract Constant Uint63.addcarryc => "MRUint63.addcarryc".
Extract Constant Uint63.subc => "MRUint63.subc".
Extract Constant Uint63.subcarryc => "MRUint63.subcarryc".

Extract Constant Uint63.diveucl => "MRUint63.diveucl".
Extract Constant Uint63.diveucl_21 => "MRUint63.div21".
Extract Constant Uint63.addmuldiv => "MRUint63.addmuldiv".

Extract Constant Uint63.compare =>
  "fun x y -> match MRUint63.compare x y with 0 -> Eq | c when c < 0 -> Lt | _ -> Gt".
Extract Constant Sint63.compare =>
  "fun x y -> match MRUint63.compares x y with 0 -> Eq | c when c < 0 -> Lt | _ -> Gt".

Extract Constant Uint63.head0 => "MRUint63.head0".
Extract Constant Uint63.tail0 => "MRUint63.tail0".
