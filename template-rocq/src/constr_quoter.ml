open Univ
open Names
open Pp
open Tm_util
open Quoter


(** The reifier to Coq values *)
module ConstrBaseQuoter =
struct
  open Constr_reification
  include ConstrReification

  let to_coq_list typ =
    let the_nil = constr_mkApp (c_nil, [| typ |]) in
    let rec to_list (ls : Constr.t list) : Constr.t =
      match ls with
	[] -> the_nil
      | l :: ls ->
	constr_mkApp (c_cons, [| typ ; l ; to_list ls |])
    in to_list

  let to_coq_listl typ = to_coq_list (Lazy.force typ)

  let rec seq f t =
    if f < t then f :: seq (f + 1) t
    else []

  let mkAnon () = Lazy.force nAnon
  let mkName id = constr_mkApp (nNamed, [| id |])

  let mkBindAnn id r = constr_mkApp (tmkBindAnn, [| id ; r |])

  let mkRel i = constr_mkApp (tRel, [| i |])
  let mkVar id = constr_mkApp (tVar, [| id |])
  let mkEvar n args = constr_mkApp (tEvar, [| n; to_coq_listl tTerm (Array.to_list args) |])
  let mkSort s = constr_mkApp (tSort, [| s |])
  let mkCast c k t = constr_mkApp (tCast, [| c ; k ; t |])
  let mkConst kn u = constr_mkApp (tConst, [| kn ; u |])
  let mkProd na t b =
    constr_mkApp (tProd, [| na ; t ; b |])
  let mkLambda na t b =
    constr_mkApp (tLambda, [| na ; t ; b |])
  let mkApp f xs =
    constr_mkApp (tApp, [| f ; to_coq_listl tTerm (Array.to_list xs) |])

  let mkLetIn na t t' b =
    constr_mkApp (tLetIn, [| na ; t ; t' ; b |])

  let mkFix ((a,b),(ns,ts,ds)) =
    let mk_fun xs i =
      constr_mkApp (tmkdef, [| Lazy.force tTerm ; Array.get ns i ;
                             Array.get ts i ; Array.get ds i ; Array.get a i |]) :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length a)) in
    let block = to_coq_list (constr_mkAppl (tdef, [| tTerm |])) (List.rev defs) in
    constr_mkApp (tFix, [| block ; b |])

  let mkConstruct (ind, i) u =
    constr_mkApp (tConstructor, [| ind ; i ; u |])

  let mkCoFix ((a,b),(ns,ts,ds)) =
    let mk_fun xs i =
      constr_mkApp (tmkdef, [| Lazy.force tTerm ; Array.get ns i ;
                             Array.get ts i ; Array.get ds i ; Array.get a i |]) :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length ns)) in
    let block = to_coq_list (constr_mkAppl (tdef, [| tTerm |])) (List.rev defs) in
    constr_mkApp (tCoFix, [| block ; b |])

  let mkInd i u = constr_mkApp (tInd, [| i ; u |])



  let mk_predicate (uinst, pars, pctx, pret) =
    let pars = to_coq_listl tTerm (Array.to_list pars) in
    let pctx = to_coq_listl taname (List.rev (Array.to_list pctx)) in
    constr_mkApp (tmk_predicate, [| Lazy.force tTerm; uinst; pars; pctx; pret |])
  let mk_branch (bctx, bbody) =
    let bctx = to_coq_listl taname (List.rev (Array.to_list bctx)) in
    constr_mkApp (tmk_branch, [| Lazy.force tTerm; bctx; bbody |])

  let mk_case_info (ind, npar, relevance) =
    constr_mkApp (mk_case_info, [| ind; npar; relevance |])

  let mkCase ci p c brs =
    let ci = mk_case_info ci in
    let p = mk_predicate p in
    let branches = List.map mk_branch brs in
    let tl = constr_mkApp (tbranchTy, [| Lazy.force tTerm |]) in
    constr_mkApp (tCase, [| ci ; p ; c ; to_coq_list tl branches |])

  let mkProj kn t =
    constr_mkApp (tProj, [| kn; t |])

  let mkInt i = i
  let mkFloat f = f
  let mkString s = s

  let mkArray u arr ~default ~ty =
    constr_mkApp (tArray, [| u; to_coq_listl tTerm (Array.to_list arr); default; ty |])

  let quote_option ty = function
    | Some tm -> constr_mkApp (cSome, [|ty; tm|])
    | None -> constr_mkApp (cNone, [|ty|])
  let quote_optionl ty = quote_option (Lazy.force ty)

  (* Quote OCaml int to Coq nat *)
  let quote_int =
    (* the cache is global but only accessible through quote_int *)
    let cache = Hashtbl.create 1023 in
    let rec recurse i =
      try Hashtbl.find cache i
      with Not_found ->
        if i = 0 then
          let result = Lazy.force tO in
          let _ = Hashtbl.add cache i result in
          result
        else
          let result = constr_mkApp (tS, [| recurse (i - 1) |]) in
          let _ = Hashtbl.add cache i result in
          result
    in
    fun i -> if i >= 0 then recurse i else
      CErrors.anomaly (str "Negative int can't be quoted to nat.")

  let quote_bool b =
    if b then Lazy.force ttrue else Lazy.force tfalse

  let quote_int63 i = constr_mkApp (tInt, [| Constr.mkInt i |])

  let quote_float64 f = constr_mkApp (tFloat, [| Constr.mkFloat f |])

  let quote_pstring s = constr_mkApp (tString, [| Constr.mkString s |])

  let quote_inductive (kn, i) =
    constr_mkApp (tmkInd, [| kn; i |])

  let byte_ind =
    lazy (let ty = Lazy.force tByte in
      match Constr.kind ty with
      | Constr.Ind (ind, u) -> ind
      | _ -> failwith "byte_ind : tByte is not bound to an inductive type")

  let quote_char i =
    Constr.UnsafeMonomorphic.mkConstruct (Lazy.force byte_ind, (i+1))

  let chars = lazy (Array.init 255 quote_char)

  let quote_char c = (Lazy.force chars).(int_of_char c)

  let string_hash = Hashtbl.create 420

  let to_string s =
    let len = String.length s in
    let rec go from acc =
      if from < 0 then acc
      else
        let term = constr_mkApp (tBsString, [| quote_char (String.get s from) ; acc |]) in
        go (from - 1) term
    in
    go (len - 1) (Lazy.force tBsEmptyString)

  let quote_string s =
    try Hashtbl.find string_hash s
    with Not_found ->
      let term = to_string s in
      Hashtbl.add string_hash s term; term

  let quote_ident i =
    let s = Id.to_string i in
    quote_string s

  let quote_relevance r =
    match r with
    | Sorts.Relevant -> Lazy.force tRelevant
    | Sorts.Irrelevant -> Lazy.force tIrrelevant
    | Sorts.RelevanceVar _ -> Lazy.force tRelevant (* TODO *)

  let quote_name n =
    match n with
      Names.Name id -> constr_mkApp (nNamed, [| quote_ident id |])
    | Names.Anonymous -> Lazy.force nAnon

  let quote_aname ann_n =
    let { Context.binder_name = n; Context.binder_relevance = relevance} = ann_n in
    let r = quote_relevance relevance in
    match n with
    | Names.Anonymous -> Constr.mkApp (Lazy.force tmkBindAnn, [|Lazy.force tname; Lazy.force nAnon; r|])
    | Names.Name id -> let nm = Constr.mkApp (Lazy.force nNamed, [| quote_ident id |]) in
                       Constr.mkApp (Lazy.force tmkBindAnn, [| Lazy.force tname; nm; r|])

  let quote_cast_kind k =
    match k with
      Constr.VMcast -> Lazy.force kVmCast
    | Constr.NATIVEcast -> Lazy.force kNative
    (* | Constr.DEFAULTcast -> Lazy.force kCast *)
    | _ -> (* FIXME *) Lazy.force kCast

  let string_of_level s =
    to_string (Univ.Level.to_string s)

  let quote_level l =
    if Level.is_set l then Lazy.force lzero
    else match Level.var_index l with
         | Some x -> constr_mkApp (tLevelVar, [| quote_int x |])
         | None -> constr_mkApp (tLevel, [| string_of_level l |])

  let quote_universe s =
    match Univ.Universe.level s with
      Some l -> constr_mkApp (tof_level, [| quote_level l |])
    | _ -> let levels = List.map (fun (l,i) -> pairl tlevel tnat (quote_level l) (quote_int i)) (Universe.repr s) in
           let hd = List.hd levels in
           let tl = to_coq_list (prodl tlevel tnat) (List.tl levels) in
           constr_mkApp (tfrom_kernel_repr, [| hd ; tl |])

  let quote_levelset s =
    let levels = Univ.Level.Set.elements s in
    let levels' =  to_coq_listl tlevel (List.map quote_level levels) in
    constr_mkApp (tLevelSet_of_list, [|levels'|])

  let quote_constraint_type (c : Univ.constraint_type) =
    match c with
    | Lt -> Lazy.force tunivLt
    | Le -> Lazy.force tunivLe0
    | Eq -> Lazy.force tunivEq

  let quote_univ_constraint ((l1, ct, l2) : Univ.univ_constraint) =
    let l1 = quote_level l1 in
    let l2 = quote_level l2 in
    let ct = quote_constraint_type ct in
    constr_mkApp (tmake_univ_constraint, [| l1; ct; l2 |])

  let quote_univ_level u = quote_level u
  (* todo : can be deduced from quote_level, hence shoud be in the Reify module *)
  let quote_univ_instance u =
    let qarr, uarr = UVars.Instance.to_array u in
    let () = if not (CArray.is_empty qarr) then
        CErrors.user_err Pp.(str "Quoting sort polymorphic instances not yet supported.")
    in
    (* we assume that valid instances do not contain [Prop] or [SProp] *)
    to_coq_listl tlevel (CArray.map_to_list quote_level uarr)

  let is_Lt = function
    | Univ.Lt -> true
    | _ -> false

  let is_Le = function
    | Univ.Le -> true
    | _ -> false

  let is_Eq = function
    | Univ.Eq -> true
    | _ -> false

   (* (Prop, Le | Lt, l),  (Prop, Eq, Prop) -- trivial, (l, c, Prop)  -- unsatisfiable  *)
  let rec constraints_ (cs : Univ.univ_constraint list) =
    match cs with
    | [] -> []
    | (l, ct, l') :: cs' ->
      quote_univ_constraint (l,ct,l') :: constraints_ cs'

  let quote_univ_constraints const =
    let const = Univ.Constraints.elements const in
    List.fold_left (fun tm c ->
        constr_mkApp (tConstraintSetadd, [| c; tm|])
      ) (Lazy.force tConstraintSetempty) (constraints_ const)

  let quote_variance v =
    match v with
    | UVars.Variance.Irrelevant -> Lazy.force cIrrelevant
    | UVars.Variance.Covariant -> Lazy.force cCovariant
    | UVars.Variance.Invariant -> Lazy.force cInvariant

  let quote_cuminfo_variance var =
    let var_list = CArray.map_to_list quote_variance var in
    to_coq_list (Lazy.force tVariance) var_list

  let quote_univ_contextset uctx =
    let levels' = quote_levelset (ContextSet.levels uctx) in
    let const' = quote_univ_constraints (ContextSet.constraints uctx) in
    pairl tLevelSet tConstraintSet levels' const'

  let quote_univ_context uctx =
    let { UVars.quals = qarr; UVars.univs = uarr} = (UVars.UContext.names uctx) in
    let () = if not (CArray.is_empty qarr) then
        CErrors.user_err Pp.(str "Quoting sort polymorphic ucontext not yet supported.")
    in
    let idents = to_coq_listl tname (CArray.map_to_list quote_name uarr) in
    let inst' = quote_univ_instance (UVars.UContext.instance uctx) in
    let const' = quote_univ_constraints (UVars.UContext.constraints uctx) in
    let p = constr_mkApp (tUContextmake', [|inst'; const'|]) in
    constr_mkApp (tUContextmake, [|idents; p |])

  (* let quote_variance_entry var =
    let listvar = constr_mkAppl (tlist, [| tVariance |]) in
    match var with
    | None -> constr_mkApp (cNone, [| listvar |])
    | Some var ->
     let var' = quote_cuminfo_variance var in
      constr_mkApp (cSome, [| listvar; var' |]) *)

 let quote_abstract_univ_context uctx =
    let { UVars.quals = qarr; UVars.univs = uarr} = (UVars.AbstractContext.names uctx) in
    let () = if not (CArray.is_empty qarr) then
        CErrors.user_err Pp.(str "Quoting sort polymorphic abstract universe context not yet supported.")
    in
    let idents = to_coq_listl tname (CArray.map_to_list quote_name uarr) in
    let const' = quote_univ_constraints (UVars.UContext.constraints (UVars.AbstractContext.repr uctx)) in
    constr_mkApp (tAUContextmake, [|idents; const'|])

  let mkMonomorphic_ctx () = Lazy.force cMonomorphic_ctx

  let mkPolymorphic_ctx t =
    constr_mkApp (cPolymorphic_ctx, [|t|])

  let mkMonomorphic_entry ctx =
     constr_mkApp (cMonomorphic_entry, [| ctx |])

  let mkPolymorphic_entry ctx =
     constr_mkApp (cPolymorphic_entry, [| ctx |])

  let quote_inductive_universes uctx =
    match uctx with
    | Entries.Monomorphic_entry ->
      let f inst = assert (UVars.Instance.is_empty inst); UVars.empty_bound_names in
      let ctx = quote_univ_context (UVars.UContext.of_context_set f Sorts.QVar.Set.empty Univ.ContextSet.empty) in
      constr_mkApp (cMonomorphic_entry, [| ctx |])
    | Entries.Polymorphic_entry uctx ->
      let ctx = quote_univ_context uctx in
      constr_mkApp (cPolymorphic_entry, [| ctx |])

  let quote_ugraph (g : UGraph.t) =
    let inst' = quote_univ_instance UVars.Instance.empty in
    let const' = quote_univ_constraints (fst (UGraph.constraints_of_universes g)) in
    let uctx = constr_mkApp (tUContextmake, [|inst' ; const'|]) in
    constr_mkApp (tadd_global_constraints, [|constr_mkApp (cMonomorphic_ctx, [| uctx |]); Lazy.force tinit_graph|])


  let sprop =
    lazy (constr_mkApp (sSProp, [|Lazy.force tuniverse |]))
  let prop =
    lazy (constr_mkApp (sProp, [|Lazy.force tuniverse |]))

  let quote_sort s = match s with
  | Sorts.Set -> constr_mkApp (sType, [| Lazy.force tuniverse; quote_universe Universe.type0 |])
  | Sorts.Prop -> Lazy.force prop
  | Sorts.SProp -> Lazy.force sprop
  | Sorts.Type u -> constr_mkApp (sType, [| Lazy.force tuniverse; quote_universe u |])
  | Sorts.QSort (_, u) -> constr_mkApp (sType, [| Lazy.force tuniverse; quote_universe u |]) (* FIXME *)

  let quote_sort_quality_or_set = function
    | UnivGen.QualityOrSet.(Qual (QConstant QProp)) -> Lazy.force sfProp
    | UnivGen.QualityOrSet.Set -> Lazy.force sfSet
    | UnivGen.QualityOrSet.(Qual (QConstant QType)) -> Lazy.force sfType
    | UnivGen.QualityOrSet.(Qual (QVar _)) -> Lazy.force sfType (* FIXME *)
    | UnivGen.QualityOrSet.(Qual (QConstant QSProp)) -> Lazy.force sfSProp

  let quote_context_decl na b t =
    constr_mkApp (tmkdecl, [| Lazy.force tTerm; na; quote_optionl tTerm b; t |])

  let quote_context ctx =
    to_coq_list (constr_mkAppl (tcontext_decl, [| tTerm |])) ctx

  let mk_ctor_list ls =
    let ctors = List.map (fun (a,b,c,d,e) ->
      constr_mkApp (tBuild_constructor_body, [| a ; b ; to_coq_listl tTerm c ; d ; e |])) ls in
    to_coq_listl tconstructor_body ctors

  let mk_proj_list ps =
    let projs = List.map (fun (a,b,c) ->
      constr_mkApp (tBuild_projection_body, [| a ; b ; c |])) ps in
    to_coq_listl tprojection_body projs

  let quote_dirpath dp =
    let l = DirPath.repr dp in
    to_coq_listl tident (List.map quote_ident l)

  let rec quote_modpath mp =
    match mp with
    | MPfile dp -> constr_mkApp (tMPfile, [|quote_dirpath dp|])
    | MPbound mbid -> let (i, id, dp) = MBId.repr mbid in
      constr_mkApp (tMPbound, [|quote_dirpath dp ; quote_ident id; quote_int i|])
    | MPdot (mp, id) -> constr_mkApp (tMPdot, [|quote_modpath mp; quote_ident (Label.to_id id)|])

  let quote_kn kn =
    pairl tmodpath tident (quote_modpath (KerName.modpath kn))
      (quote_ident (Label.to_id (KerName.label kn)))

  let quote_proj ind pars args =
    constr_mkApp (tmkProjection, [| ind; pars; args |])

  let mk_one_inductive_body (na, indices, sort, ty, sf, ctors, projs, relevance) =
    let ctors = mk_ctor_list ctors in
    let projs = mk_proj_list projs in
    constr_mkApp (tBuild_one_inductive_body, [| na; indices; sort; ty; sf; ctors; projs; relevance |])

  let to_coq_option ty f ind =
    match ind with
    | None -> constr_mkApp (cNone, [| ty |])
    | Some x -> constr_mkApp (cSome, [| ty; f x |])

  let mk_mutual_inductive_body finite npars params inds uctx var =
    let inds = to_coq_listl tone_inductive_body inds in
    let var = to_coq_option (constr_mkAppl (tlist, [| tVariance |])) (to_coq_listl tVariance) var in
    constr_mkApp (tBuild_mutual_inductive_body, [|finite; npars; params; inds; uctx; var|])

  let mk_constant_body ty tm uctx rel =
    let tm = quote_optionl tTerm tm in
    constr_mkApp (tBuild_constant_body, [|ty; tm; uctx; rel|])

  let mk_inductive_decl mind =
    constr_mkApp (tInductiveDecl, [|mind|])

  let mk_constant_decl bdy =
    constr_mkApp (tConstantDecl, [|bdy|])

  let global_pairty () =
    constr_mkAppl (prod_type, [| tkername; tglobal_decl |])

  let empty_global_declarations () =
    constr_mkApp (c_nil, [| global_pairty () |])

  let add_global_decl kn d l =
    let pair = pairl tkername tglobal_decl kn d in
    constr_mkApp (c_cons, [| global_pairty (); pair; l|])

  type pre_quoted_retroknowledge =
    { retro_int63 : quoted_kernel_name option;
      retro_float64 : quoted_kernel_name option;
      retro_string : quoted_kernel_name option;
      retro_array : quoted_kernel_name option }

  let quote_retroknowledge r =
    let rint63 = to_coq_option (Lazy.force tkername) (fun x -> x) r.retro_int63 in
    let rfloat64 = to_coq_option (Lazy.force tkername) (fun x -> x) r.retro_float64 in
    let rstring = to_coq_option (Lazy.force tkername) (fun x -> x) r.retro_string in
    let rarray = to_coq_option (Lazy.force tkername) (fun x -> x) r.retro_array in
    constr_mkApp (tmk_retroknowledge, [| rint63; rfloat64; rstring; rarray |])

  let mk_global_env univs decls retro =
    constr_mkApp (tBuild_global_env, [| univs; decls; retro |])

  let mk_program f s = pairl tglobal_env tTerm f s

  let quote_mind_finiteness (f: Declarations.recursivity_kind) =
    match f with
    | Declarations.Finite -> Lazy.force cFinite
    | Declarations.CoFinite -> Lazy.force cCoFinite
    | Declarations.BiFinite -> Lazy.force cBiFinite

  let make_one_inductive_entry (iname, arity, consnames, constypes) =
    let consnames = to_coq_listl tident consnames in
    let constypes = to_coq_listl tTerm constypes in
    constr_mkApp (tBuild_one_inductive_entry, [| iname; arity; consnames; constypes |])

  let quote_mutual_inductive_entry (mf, mp, is, mpol, var) =
    let is = to_coq_listl tOne_inductive_entry (List.map make_one_inductive_entry is) in
    let mpr = constr_mkAppl (cNone, [|bool_type|]) in
    let mr = constr_mkApp (cNone, [|constr_mkAppl (option_type, [|tident|])|]) in
    let var = quote_option (constr_mkAppl (tlist, [| tVariance |]))
        (Option.map (fun var ->
             let var = List.map (quote_option (Lazy.force tVariance)) var in
             to_coq_listl tVariance var)
            var)
    in
    constr_mkApp (tBuild_mutual_inductive_entry, [| mr; mf; mp; is; mpol; var; mpr |])

  let quote_parameter_entry ty univs =
    constr_mkApp (cBuild_parameter_entry, [|ty; univs|])

  let quote_definition_entry ty body univs =
    constr_mkApp (cBuild_definition_entry, [| quote_option (Lazy.force tTerm) ty; body; univs|])

  let quote_constant_entry = function
    | Left ce ->  constr_mkApp (cDefinitionEntry, [| ce |])
    | Right pe -> constr_mkApp (cParameterEntry, [| pe |])

  let quote_entry decl =
    let opType = constr_mkAppl(sum_type, [|tConstant_entry;tMutual_inductive_entry|]) in
    let mkSome c t = constr_mkApp (cSome, [|opType; constr_mkAppl (c, [|tConstant_entry;tMutual_inductive_entry; lazy t|] )|]) in
    let mkSomeDef = mkSome cInl in
    let mkSomeInd  = mkSome cInr in
    match decl with
    | Some (Left centry) -> mkSomeDef (quote_constant_entry centry)
    | Some (Right mind) -> mkSomeInd mind
    | None -> constr_mkApp (cNone, [| opType |])


  let quote_global_reference : Names.GlobRef.t -> quoted_global_reference = function
    | Names.GlobRef.VarRef v ->
       let id = quote_ident v in
       constr_mkApp (tVarRef, [|id|])
    | Names.GlobRef.ConstRef c ->
       let kn = quote_kn (Names.Constant.canonical c) in
       constr_mkApp (tConstRef, [|kn|])
    | Names.GlobRef.IndRef (i, n) ->
       let kn = quote_kn (Names.MutInd.canonical i) in
       let n = quote_int n in
       constr_mkApp (tIndRef, [|quote_inductive (kn ,n)|])
    | Names.GlobRef.ConstructRef ((i, n), k) ->
       let kn = quote_kn (Names.MutInd.canonical i) in
       let n = quote_int n in
       let k = (quote_int (k - 1)) in
       constr_mkApp (tConstructRef, [|quote_inductive (kn ,n); k|])
end


module ConstrQuoter = Quoter(ConstrBaseQuoter)

include ConstrBaseQuoter
include ConstrQuoter
