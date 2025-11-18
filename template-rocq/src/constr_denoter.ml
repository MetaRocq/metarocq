open Pp
open Names
open Tm_util
open Denoter


module ConstrBaseDenoter =
struct
  open Constr_reification
  include ConstrReification

  let unquote_sigt trm =
    let (h,args) = app_full trm [] in
    if constr_equall h texistT then
      match args with
        _ :: _ :: x :: y :: [] -> (x, y)
      | _ -> bad_term_verb trm "unquote_sigt"
    else
      not_supported_verb trm "unquote_sigt"

  let unquote_pair trm =
    let (h,args) = app_full trm [] in
    if constr_equall h c_pair then
      match args with
        _ :: _ :: x :: y :: [] -> (x, y)
      | _ -> bad_term_verb trm "unquote_pair"
    else
      not_supported_verb trm "unquote_pair"

  let unquote_case_info trm =
    let (h,args) = app_full trm [] in
    if constr_equall h mk_case_info then
      match args with
      | ind :: nparam :: relevance :: [] ->
        { aci_ind = ind;
          aci_npar = nparam;
          aci_relevance = relevance }
      | _ -> bad_term_verb trm "unquote_case_info"
    else
      not_supported_verb trm "unquote_case_info"

  let rec unquote_list trm =
    let (h,args) = app_full trm [] in
    if constr_equall h c_nil then
      []
    else if constr_equall h c_cons then
      match args with
        _ :: x :: xs :: [] -> x :: unquote_list xs
      | _ -> bad_term_verb trm "unquote_list"
    else
      not_supported_verb trm "unquote_list"

  (* Unquote Coq nat to OCaml int *)
  let rec unquote_nat trm =
    let (h,args) = app_full trm [] in
    if constr_equall h tO then
      0
    else if constr_equall h tS then
      match args with
        n :: [] -> 1 + unquote_nat n
      | _ -> bad_term_verb trm "unquote_nat"
    else
      not_supported_verb trm "unquote_nat"

  let unquote_bool trm =
    if constr_equall trm ttrue then
      true
    else if constr_equall trm tfalse then
      false
    else not_supported_verb trm "from_bool"

  let unquote_int63 trm =
    match Constr.kind trm with
    | Constr.Int i -> i
    | _ -> not_supported_verb trm "unquote_int63"

  let unquote_float64 trm =
    match Constr.kind trm with
    | Constr.Float f -> f
    | _ -> not_supported_verb trm "unquote_float64"

  let unquote_pstring trm =
    match Constr.kind trm with
    | Constr.String s -> s
    | _ -> not_supported_verb trm "unquote_pstring"

  let unquote_char trm =
    let (h,args) = app_full trm [] in
    match Constr.kind h with
    | Constr.Construct ((ind, idx), u) -> Char.chr (idx - 1)
    | _ -> not_supported_verb trm "unquote_char"

  let unquote_string trm =
    let rec go n trm =
      let (h,args) = app_full trm [] in
      if constr_equall h tBsEmptyString then
        Bytes.create n
      else if constr_equall h tBsString then
        match args with
          c :: s :: [] ->
          let res = go (n + 1) s in
          let _ = Bytes.set res n (unquote_char c) in
          res
        | _ -> bad_term_verb trm "unquote_string"
      else
        not_supported_verb trm "unquote_string"
    in
    Bytes.to_string (go 0 trm)


  let unquote_ident trm =
    Names.Id.of_string (unquote_string trm)

  let unquote_cast_kind trm =
    if constr_equall trm kVmCast then
      Constr.VMcast
    else if constr_equall trm kCast then
      Constr.DEFAULTcast
    else if constr_equall trm kNative then
      Constr.VMcast
    else
      not_supported_verb trm "unquote_cast_kind"

  let unquote_name trm =
    let (h,args) = app_full trm [] in
    if constr_equall h nAnon then
      Names.Anonymous
    else if constr_equall h nNamed then
      match args with
        n :: [] -> Names.Name (unquote_ident n)
      | _ -> bad_term_verb trm "unquote_name"
    else
      not_supported_verb trm "unquote_name"

  let unquote_evar env evm id args =
    if constr_equall id tfresh_evar_id then
      let evm, (tyev, s) = Evarutil.new_type_evar env evm Evd.univ_flexible_alg in
      let evm, ev = Evarutil.new_evar env evm tyev in
      evm, EConstr.Unsafe.to_constr ev
    else
      let id = unquote_nat id in
      let ev = Evar.unsafe_of_int id in
      evm, Constr.mkEvar (ev, SList.of_full_list args)

  let unquote_relevance trm =
    if Constr.equal trm (Lazy.force tRelevant) then
      Sorts.Relevant
    else if Constr.equal trm (Lazy.force tIrrelevant) then
      Sorts.Irrelevant
    else raise (Failure "Invalid relevance")

  let unquote_aname trm =
    let (h,args) = app_full trm [] in
    if Constr.equal h (Lazy.force tmkBindAnn) then
      match args with
        _ :: nm :: relevance :: _ -> { Context.binder_name = unquote_name nm; Context.binder_relevance = unquote_relevance relevance }
      | _ -> bad_term_verb trm "unquote_aname"
    else
      not_supported_verb trm "unquote_aname"

  let get_level evm s =
    if CString.string_contains ~where:s ~what:"." then
      match List.rev (CString.split_on_char '.' s) with
      | [] -> CErrors.anomaly (str"Invalid universe name " ++ str s ++ str".")
      | n :: dp ->
        let num = int_of_string n in
        let dp = DirPath.make (List.map Id.of_string dp) in
        (* TODO handle univs created in workers *)
        let l = Univ.Level.make (Univ.UGlobal.make dp "" num) in
        try
          let evm = Evd.add_forgotten_univ evm l in
          if !strict_unquote_universe_mode then
            CErrors.user_err (str ("Level "^s^" is not a declared level and you are in Strict Unquote Universe Mode."))
          else (evm, l)
        with
        | UGraph.AlreadyDeclared -> evm, l
    else
      try
        evm, Evd.universe_of_name evm (Id.of_string s)
      with Not_found ->
      try
        let univ = Nametab.locate_universe (Libnames.qualid_of_string s) in
        evm, Univ.Level.make univ
      with Not_found ->
        CErrors.user_err (str ("Level "^s^" is not a declared level."))

  let is_fresh_level evm trm h args =
    if constr_equall h tLevel then
      match args with
      | s :: [] -> debug (fun () -> str "Unquoting level " ++ Printer.pr_constr_env (Global.env ()) evm trm);
        let s = (unquote_string s) in
        s = "__metarocq_fresh_level__"
      | _ -> bad_term_verb trm "unquote_level"
    else false

  let unquote_level evm trm (* of type level *) : Evd.evar_map * Univ.Level.t =
    let (h,args) = app_full trm [] in
    if is_fresh_level evm trm h args then
      if !strict_unquote_universe_mode then
        CErrors.user_err (str "It is not possible to unquote a fresh level in Strict Unquote Universe Mode.")
      else
        let evm, l = Evd.new_univ_level_variable (Evd.UnivFlexible false) evm in
        debug (fun () -> str"Fresh level " ++ Univ.Level.raw_pr l ++ str" was added to the context.");
        evm, l
    else if constr_equall h lzero then
      match args with
      | [] -> evm, Univ.Level.set
      | _ -> bad_term_verb trm "unquote_level"
    else if constr_equall h tLevel then
      match args with
      | s :: [] -> debug (fun () -> str "Unquoting level " ++ Printer.pr_constr_env (Global.env ()) evm trm);
        get_level evm (unquote_string s)
      | _ -> bad_term_verb trm "unquote_level"
    else if constr_equall h tLevelVar then
      match args with
      | l :: [] -> evm, Univ.Level.var (unquote_nat l)
      | _ -> bad_term_verb trm "unquote_level"
    else
      not_supported_verb trm "unquote_level"

  let unquote_universe_level = unquote_level

  let iter_int f a n =
    if n < 0 then failwith "Negative number of iterations"
    else
      let rec loop f a = function 0 -> a | n -> loop f (f a) (n-1)
      in
      loop f a n


  let unquote_univ_expr evm trm (* of type LevelExpr.t *) : Evd.evar_map * Univ.Universe.t =
    let (h,args) = app_full trm [] in
    if constr_equall h c_pair then
      let l, b = unquote_pair trm in
      let evm, l' = unquote_level evm l in
      let u = Univ.Universe.make l' in
      evm, iter_int Univ.Universe.super u (unquote_nat b)
    else
      not_supported_verb trm "unquote_univ_expr"

  let unquote_universe evm trm (* of type universe *) =
    let (h,args) = app_full trm [] in
    if constr_equall h tBuild_Universe then
      (match args with
      | x :: _ :: [] ->
        (let (h,args) = app_full x [] in
        if constr_equall h tMktLevelExprSet then
          match args with
          | x :: _ :: [] ->
              (match unquote_list x with
              | [] -> assert false
              | e::q ->
                let evm, u = List.fold_left (fun (evm,u) e ->
                            let evm, u' = unquote_univ_expr evm e
                            in evm, Univ.Universe.sup u u')
                          (unquote_univ_expr evm e) q
                in evm, u)
          | _ -> bad_term_verb trm "unquote_universe 0"
        else
          not_supported_verb trm "unquote_universe 0")
      | _ -> bad_term_verb trm "unquote_universe 1")
    else not_supported_verb trm "unquote_universe 2"

  let unquote_sort evm trm (* of type sort *) =
    let (h,args) = app_full trm [] in
    if constr_equall h sSProp then
      match args with
         | [_univ] -> evm, Sorts.sprop
         | _ -> bad_term_verb trm "unquote_sort_sprop_args"
    else if constr_equall h sProp then
      match args with
         | [_univ] -> evm, Sorts.prop
         | _ -> bad_term_verb trm "unquote_sort_prop_args"
    else if constr_equall h sType then
      match args with
      | [_univ; x] ->
          let evm, u = unquote_universe evm x in
          evm, Sorts.sort_of_univ u
      | _ -> bad_term_verb trm "unquote_sort_type_too_many_args"
    else bad_term_verb trm "unquote_sort_type_no_args"

  let unquote_universe_instance evm trm (* of type universe_instance *) =
    let l = unquote_list trm in
    let evm, l = map_evm unquote_universe evm l in
    let l = List.map (fun u ->
        match Univ.Universe.level u with
        | Some l -> l
        | None -> bad_term_verb trm "unquote_universe_instance_not_level") l
    in
    evm, UVars.Instance.of_array ([||], Array.of_list l)

  let unquote_variance v =
    let open UVars.Variance in
    if constr_equall v cIrrelevant then Irrelevant
    else if constr_equall v cCovariant then Covariant
    else if constr_equall v cInvariant then Invariant
    else not_supported_verb v "unquote_variance"

  let unquote_dirpath dp : DirPath.t =
    let l = List.map unquote_ident (unquote_list dp) in
    DirPath.make l

  let rec unquote_modpath mp : ModPath.t =
    let (h,args) = app_full mp [] in
    if constr_equall h tMPfile then
      match args with
      | dp::[] -> ModPath.MPfile (unquote_dirpath dp)
      | _ -> bad_term_verb mp "unquote_modpath"
    else if constr_equall h tMPbound then
      match args with
      | dp::id::i::[] ->
        ModPath.MPbound (Obj.magic (unquote_nat i, unquote_ident id, unquote_dirpath dp) : MBId.t)
      | _ -> bad_term_verb mp "unquote_modpath"
    else if constr_equall h tMPdot then
      match args with
      | mp'::id::[] -> ModPath.MPdot (unquote_modpath mp', Label.of_id (unquote_ident id))
      | _ -> bad_term_verb mp "unquote_modpath"
    else
      not_supported_verb mp "unquote_modpath"

  let unquote_kn (k : quoted_kernel_name) : KerName.t =
    let (mp, id) = unquote_pair k in
    KerName.make (unquote_modpath mp) (Label.of_id (unquote_ident id))

  let unquote_proj (qp : quoted_proj) : (quoted_inductive * quoted_int * quoted_int) =
    let (h,args) = app_full qp [] in
    if constr_equall h tmkProjection then
      match args with
      | ind :: nm :: num :: [] -> (ind, nm, num)
      | _ -> bad_term_verb qp "unquote_proj"
    else not_supported_verb qp "unquote_proj"

  let unquote_inductive trm : inductive =
    let (h,args) = app_full trm [] in
    if constr_equall h tmkInd then
      match args with
      | nm :: num :: [] -> Names.MutInd.make1 (unquote_kn nm), unquote_nat num
      | _ -> bad_term_verb trm "unquote_inductive"
    else
      not_supported_verb trm "unquote_inductive"


  let unquote_int = unquote_nat
  let print_term x = Printer.pr_constr_env (Global.env ()) Evd.empty x


  let unquote_global_reference (trm : Constr.t) (* of type global_reference *) : GlobRef.t =
    let (h,args) = app_full trm [] in
    if constr_equall h tVarRef then
      match args with
      | id :: [] -> GlobRef.VarRef (unquote_ident id)
      | _ -> bad_term_verb trm "unquote_global_reference"
    else if constr_equall h tConstRef then
      match args with
      | kn :: [] -> GlobRef.ConstRef (Constant.make1 (unquote_kn kn))
      | _ -> bad_term_verb trm "unquote_global_reference"
    else if constr_equall h tIndRef then
      match args with
      | ind :: [] -> GlobRef.IndRef (unquote_inductive ind)
      | _ -> bad_term_verb trm "unquote_global_reference"
    else if constr_equall h tConstructRef then
      match args with
      | ind :: c :: [] -> GlobRef.ConstructRef (unquote_inductive ind, unquote_nat c + 1)
      | _ -> bad_term_verb trm "unquote_global_reference"
    else
      not_supported_verb trm "unquote_global_reference"

  let unquote_branch trm =
    let (h, args) = app_full trm [] in
    if constr_equall h tmk_branch then
      match args with
      | _ty :: bctx :: bbody :: [] ->
      { abcontext = unquote_list bctx; abbody = bbody }
      | _ -> bad_term_verb trm "unquote_branch"
    else not_supported_verb trm "unquote_branch"

  let unquote_predicate trm =
    let (h, args) = app_full trm [] in
    if constr_equall h tmk_predicate then
      match args with
      | _ty :: auinst :: apars :: apcontext :: apreturn :: [] ->
        let apars = unquote_list apars in
        let apcontext = unquote_list apcontext in
        { auinst; apars; apcontext; apreturn }
      | _ -> bad_term_verb trm "unquote_predicate"
    else not_supported_verb trm "unquote_predicate"

  let inspect_term (t:Constr.t)
  : (Constr.t, quoted_int, quoted_ident, quoted_name, quoted_sort, quoted_cast_kind, quoted_kernel_name,
    quoted_inductive, quoted_relevance, quoted_universe, quoted_univ_instance, quoted_proj,
    quoted_int63, quoted_float64, quoted_pstring) structure_of_term =
    (* debug (fun () -> Pp.(str "denote_term" ++ spc () ++ print_term t)) ; *)
    let (h,args) = app_full t [] in
    if constr_equall h tRel then
      match args with
        x :: _ -> ACoq_tRel x
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tVar then
      match args with
        x :: _ -> ACoq_tVar x
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tEvar then
      match args with
      | [x; y] -> ACoq_tEvar (x, unquote_list y)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tSort then
      match args with
        x :: _ -> ACoq_tSort x
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tCast then
      match args with
        x :: y :: z :: _ -> ACoq_tCast (x, y, z)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tProd then
      match args with
        n :: t :: b :: _ -> ACoq_tProd (n,t,b)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tLambda then
      match args with
        n  :: t :: b :: _ -> ACoq_tLambda (n,t,b)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tLetIn then
      match args with
        n :: e :: t :: b :: _ -> ACoq_tLetIn (n,e,t,b)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tApp then
      match args with
        f::xs::_ -> ACoq_tApp (f, unquote_list xs)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tConst then
      match args with
        s::u::_ -> ACoq_tConst (s, u)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tInd then
      match args with
        i::u::_ -> ACoq_tInd (i,u)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tConstructor then
      match args with
        i::idx::u::_ -> ACoq_tConstruct (i,idx,u)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure: constructor case"))
    else if constr_equall h tCase then
      match args with
        info::p::d::brs::_ -> ACoq_tCase (unquote_case_info info, unquote_predicate p, d,
           List.map unquote_branch (unquote_list brs))
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tFix then
      match args with
        bds::i::_ ->
        let unquoteFbd  b  =
          let (_,args) = app_full b [] in
          match args with
          | _(*type*) :: na :: ty :: body :: rarg :: [] ->
            { adtype = ty;
              adname = na;
              adbody = body;
              rarg
            }
          |_ -> raise (Failure " (mkdef must take exactly 5 arguments)")
        in
        let lbd = List.map unquoteFbd (unquote_list bds) in
        ACoq_tFix (lbd, i)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tCoFix then
      match args with
        bds::i::_ ->
        let unquoteFbd  b  =
          let (_,args) = app_full b [] in
          match args with
          | _(*type*) :: na :: ty :: body :: rarg :: [] ->
            { adtype = ty;
              adname = na;
              adbody = body;
              rarg
            }
          |_ -> raise (Failure " (mkdef must take exactly 5 arguments)")
        in
        let lbd = List.map unquoteFbd (unquote_list bds) in
        ACoq_tCoFix (lbd, i)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tProj then
      match args with
        proj::t::_ -> ACoq_tProj (proj, t)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tInt then
      match args with
        t::_ -> ACoq_tInt t
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tFloat then
      match args with
        t::_ -> ACoq_tFloat t
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tString then
      match args with
        t::_ -> ACoq_tString t
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tArray then
      match args with
        u::v::def::ty::_ -> ACoq_tArray (u, Array.of_list (unquote_list v), def, ty)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else
      CErrors.user_err (str"inspect_term: cannot recognize " ++ print_term t ++ str" (maybe you forgot to reduce it?)")

end



module ConstrDenoter = Denoter(ConstrBaseDenoter)

include ConstrBaseDenoter
include ConstrDenoter
