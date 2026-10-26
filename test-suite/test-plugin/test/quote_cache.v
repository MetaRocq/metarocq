From MetaRocq.TestPlugin Require Import Loader.

(* The quoter caches the quoted value of each kernel subterm by physical
   equality. The commands build their kernel terms in OCaml and fail with an
   error if the cache contract does not hold. *)

(* A term with 2^60 tree nodes and 61 distinct nodes. Without sharing, its
   repeated leaf is quoted twice, and the command fails at once. *)
MetaRocq Test Quotation Sharing.

(* More distinct subterms than the cache keeps, so the table resizes and
   evicts. Quotations through one cache and through a fresh one are equal. *)
MetaRocq Test Quotation Cache.

(* Deep telescopes whose levels differ only in their binder names must not
   share one cache slot. *)
MetaRocq Test Quotation Telescopes.
