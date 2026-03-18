From Stdlib Require Import List.
From MetaRocq.Template Require Import All.

Import ListNotations.
Import MonadNotation.
Open Scope bs_scope.
Definition qlist := Eval compute in match <% list %> with
    | tInd ind _ => ind.(inductive_mind)
    | _ => (MPfile nil, ""%bs)
    end.


Definition refresh_sort t :=
  match t with
  | tSort s => tSort (Sort.map (fun _ => fresh_universe) s)
  | _ => t
  end.

Definition refresh_arity s :=
  let (ctx, concl) := decompose_prod_assum [] s in
  it_mkProd_or_LetIn ctx (refresh_sort concl).

  Definition mind_body_to_entry :=
  fun decl : mutual_inductive_body =>
  {|
  mind_entry_record := None;
  mind_entry_finite := Finite;
  mind_entry_params :=
      match hd_error (ind_bodies decl) with
      | Some i0 =>
          List.rev
          (let typ := decompose_prod (ind_type i0) in
              let (a, b) := typ in
              (fun p : list aname × list term =>
              let (a0, b0) := p in
              (fun (names : list aname) (types : list term) (_ : term) =>
              let names0 := firstn (ind_npars decl) names in
              let types0 := firstn (ind_npars decl) types in
              map (fun '(x, ty) => vass x ty) (combine names0 types0)) a0 b0)
              a b)
      | None => []
      end;
  mind_entry_inds :=
      map
      (fun X : one_inductive_body =>
          match X with
          | {|
              ind_name := ind_name;
              ind_indices := ind_indices;
              ind_sort := ind_sort;
              ind_type := ind_type;
              ind_kelim := ind_kelim;
              ind_ctors := ind_ctors;
              ind_projs := ind_projs;
              ind_relevance := ind_relevance
          |} =>
              {|
              mind_entry_typename := ind_name;
              mind_entry_arity := refresh_arity (remove_arity (ind_npars decl) ind_type);
              mind_entry_consnames :=
                  map (fun x : constructor_body => cstr_name x) ind_ctors;
              mind_entry_lc :=
                  map
                  (fun x : constructor_body =>
                      remove_arity (ind_npars decl) (cstr_type x)) ind_ctors
              |}
          end) (ind_bodies decl);
  mind_entry_universes := universes_entry_of_decl (ind_universes decl);
  mind_entry_template := false;
  mind_entry_variance := option_map (map Some) (ind_variance decl);
  mind_entry_private := None
  |}.



Unset MetaRocq Strict Unquote Universe Mode.
MetaRocq Run (tmQuoteInductive qlist >>= fun mib =>
  let entry := mind_body_to_entry mib in
  entry <- tmEval all entry;;
  tmPrint entry ;;
  tmMkInductive true entry).
