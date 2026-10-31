let nat_of_caml_int i =
  let rec aux acc i =
    if i < 0 then acc
    else aux (Datatypes.S acc) (i - 1)
  in aux Datatypes.O (i - 1)

let rec iter_nat f acc = function
  | Datatypes.O -> acc
  | Datatypes.S x -> iter_nat f (f acc) x

let caml_int_of_nat n = iter_nat succ 0 n
