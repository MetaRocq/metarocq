(*
Printf.printf "let int_of_byte = \n";;

for i = 0 to 255 do
  Printf.printf "| Coq_x%02x -> %i\n" i i
done *)
(*
Printf.printf "open Byte\n";;

Printf.printf "let char_of_byte = function\n";;

for i = 0 to 255 do
  Printf.printf "| Coq_x%02x -> '\\%03i'\n" i i
done;;

Printf.printf "let byte_of_char = function\n";;
for i = 0 to 255 do
  Printf.printf "| '\\%03i' -> Coq_x%02x\n" i i
done;;
*)
(*
Printf.printf "From Stdlib Require Import Byte.\n\n";;

for i = 0 to 255 do
  Printf.printf "Definition is_byte_x%02x (b : byte) := match b with | x%02x => true | _ => false end.\n" i i
done;;

Printf.printf "Definition eqb (b b' : byte) :=\n  match b with\n";;

for i = 0 to 255 do
  Printf.printf "  | x%02x => is_byte_x%02x b'\n" i i
done;;
Printf.printf"  end.\n";;

for i = 0 to 255 do
  Printf.printf "Definition compare_byte_x%02x (b : byte) :=\n" i;
  Printf.printf "  match b with\n";
  if i != 0 then Printf.printf "  ";
  for j = 0 to i - 1 do
    Printf.printf "| x%02x " j
  done;
  if i != 0 then Printf.printf "=> Gt\n";
  Printf.printf "  | x%02x => Eq\n" i;
  if i != 255 then
    Printf.printf "  | _ => Lt\n";
  Printf.printf "  end.\n"
done;;

Printf.printf "Definition compare (b b' : byte) :=\n  match b with\n";;

for i = 0 to 255 do
  Printf.printf "  | x%02x => compare_byte_x%02x b'\n" i i
done;;
Printf.printf"  end.\n";;
*)


for i = 0 to 255 do
  Printf.printf "| x%02x -> <%%x%02x%%>\n" i i
done
