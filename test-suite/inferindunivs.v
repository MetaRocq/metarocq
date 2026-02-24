From Stdlib Require Import List.
From MetaRocq.Template Require Import All Loader.
Import Ast.Env.
Import ListNotations.
Import MonadNotation.

Local Open Scope bs_scope.

Definition bnamed n := {| binder_name := nNamed n; binder_relevance := Relevant |}.

MetaRocq Quote Definition rid := @id.

Universe u.
MetaRocq Quote Definition qu := Type@{u}.
Universe v.
MetaRocq Quote Definition qv := Type@{v}.

Universe w.
MetaRocq Quote Definition qw := Type@{w}.

Definition update_mutual_inductive_entry_inds (mie : mutual_inductive_entry) inds' :=
 {| mind_entry_record := mie.(mind_entry_record);
	mind_entry_finite := mie.(mind_entry_finite);
    mind_entry_params := mie.(mind_entry_params);
    mind_entry_inds := inds';
    mind_entry_universes := mie.(mind_entry_universes);
    mind_entry_template := mie.(mind_entry_template);
    mind_entry_variance := mie.(mind_entry_variance);
    mind_entry_private := mie.(mind_entry_private) |}.

Definition add_cstr_univs (mie : mutual_inductive_entry) :=
  let inds := mie.(mind_entry_inds) in
  let add_cstr oie :=
    let cstrs := oie.(mind_entry_lc) in
    let cstr' :=
      it_mkProd_or_LetIn mie.(mind_entry_params)
        (tProd (bnamed "newty"%bs) qv
          (tProd (bnamed "new") (mkApps rid [qu; tRel 0])
            (mkApps (tRel (2 + List.length (mie.(mind_entry_params))))
              (to_extended_list mie.(mind_entry_params)))))
    in
    let prime_cstrs := List.map (fun s => s ++ "'") oie.(mind_entry_consnames) in
    {| mind_entry_typename := (oie.(mind_entry_typename) ++ "'");
       mind_entry_arity := (*oie.(mind_entry_arity)*) qw;
       mind_entry_lc := cstr' :: cstrs;
       mind_entry_consnames := "newcons" :: prime_cstrs |}
  in
  let inds' := List.map add_cstr inds in
  update_mutual_inductive_entry_inds mie inds'.

Inductive foo : Set :=
 | bar : foo.

Definition fooref := (MPfile ["inferindunivs"; "TestSuite"; "MetaRocq"], "foo").

MetaRocq Run (tmQuoteInductive fooref >>= fun mib =>
    let mie := mind_body_to_entry mib in
    let mie := add_cstr_univs mie in
    tmMkInductive true mie).

Set Printing Universes.
Set Printing All.

Print foo'.
