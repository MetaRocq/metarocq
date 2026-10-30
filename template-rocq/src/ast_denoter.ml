open Names
open Constr
open Kernames
open BasicAst
open Ast0
open Env
open Tm_util

module BaseExtractionDenoter =
struct
  type t = Ast0.term
  type quoted_ident = Bytestring.String.t
  type quoted_int = Datatypes.nat
  type quoted_int63 = Uint63.t
  type quoted_float64 = Float64.t
  type quoted_pstring = Pstring.t
  type quoted_bool = bool
  type quoted_name = name
  type quoted_aname = name binder_annot
  type quoted_relevance = relevance
  type quoted_sort = Universes0.Sort.t
  type quoted_cast_kind = cast_kind
  type quoted_kernel_name = kername
  type quoted_inductive = inductive
  type quoted_proj = projection
  type quoted_global_reference = global_reference

  type quoted_sort_quality_or_set = Universes0.allowed_eliminations
  type quoted_constraint_type = Universes0.ConstraintType.t
  type quoted_univ_constraint = Universes0.UnivConstraint.t
  type quoted_univ_constraints = Universes0.ConstraintSet.t
  type quoted_univ_level = Universes0.Level.t
  type quoted_univ_instance = Universes0.Instance.t
  type quoted_univ_context = Universes0.UContext.t
  type quoted_contextset = Universes0.ContextSet.t
  type quoted_abstract_univ_context = Universes0.AUContext.t
  type quoted_variance = Universes0.Variance.t
  type quoted_universes_decl = Universes0.universes_decl
  type quoted_universes_entry = Universes0.universes_entry

  type quoted_ind_entry = quoted_ident * t * quoted_ident list * t list
  type quoted_definition_entry = Ast0.definition_entry
  type quoted_parameter_entry = Ast0.parameter_entry
  type quoted_constant_entry = Ast0.constant_entry
  type quoted_mind_entry = mutual_inductive_entry
  type quoted_mind_finiteness = recursivity_kind
  type quoted_entry = (constant_entry, quoted_mind_entry) sum option

  type quoted_context_decl = t context_decl
  type quoted_context = context
  type quoted_one_inductive_body = one_inductive_body
  type quoted_mutual_inductive_body = mutual_inductive_body
  type quoted_constant_body = constant_body
  type quoted_global_decl = global_decl
  type quoted_global_declarations = (kername * global_decl) list
  type quoted_retroknowledge = Environment.Retroknowledge.t
  type quoted_global_env = global_env
  type quoted_program = program

  type quoted_hint_locality = Hints.hint_locality

  let mkAnon = Ast_quoter.mkAnon
  let mkName = Ast_quoter.mkName
  let mkRel = mkRel
  let mkVar = mkVar
  let mkEvar = mkEvar
  let mkSort = mkSort
  let mkCast = mkCast
  let mkProd = mkProd

  let mkLambda = mkLambda
  let mkApp = mkApp
  let mkLetIn = mkLetIn
  let mkFix = mkFix
  let mkCoFix = mkCoFix
  let mkCase = mkCase
  let mkProj = mkProj
  let mkInt = mkInt
  let mkFloat = mkFloat

  let unquote_def (x: 't BasicAst.def) : ('t, name binder_annot, quoted_int) adef =
    {
      adname=dname x;
      adtype=dtype x;
      adbody=dbody x;
      rarg=rarg x
    }

  let unquote_predicate (x: 't Ast0.predicate) : ('t, quoted_aname, quoted_univ_instance) apredicate =
    {
      auinst = puinst x;
      apars = pparams x;
      apcontext = pcontext x;
      apreturn = preturn x
    }

  let unquote_branch (x : 't Ast0.branch) : ('t, quoted_aname) abranch =
    { abcontext = bcontext x;
      abbody = bbody x }

  let unquote_case_info (x : BasicAst.case_info) : (quoted_int, quoted_inductive, quoted_relevance) acase_info =
    { aci_ind = x.ci_ind;
      aci_npar = x.ci_npar;
      aci_relevance = x.ci_relevance }

  let inspect_term (tt: t):(t, quoted_int, quoted_ident, quoted_aname, quoted_sort, quoted_cast_kind,
    quoted_kernel_name, quoted_inductive, quoted_relevance, quoted_univ_level, quoted_univ_instance, quoted_proj,
    quoted_int63, quoted_float64, quoted_pstring) structure_of_term =
    match tt with
    | Coq_tRel n -> ACoq_tRel n
    | Coq_tVar v -> ACoq_tVar v
    | Coq_tEvar (x,l) -> ACoq_tEvar (x,l)
    | Coq_tSort u -> ACoq_tSort u
    | Coq_tCast (t,k,tt) -> ACoq_tCast (t,k,tt)
    | Coq_tProd (a,b,c) -> ACoq_tProd (a,b,c)
    | Coq_tLambda (a,b,c) -> ACoq_tLambda (a,b,c)
    | Coq_tLetIn (a,b,c,d) -> ACoq_tLetIn (a,b,c,d)
    | Coq_tApp (a,b) -> ACoq_tApp (a,b)
    | Coq_tConst (a,b) -> ACoq_tConst (a,b)
    | Coq_tInd (a,b) -> ACoq_tInd (a,b)
    | Coq_tConstruct (a,b,c) -> ACoq_tConstruct (a,b,c)
    | Coq_tCase (a,b,c,d) ->
      ACoq_tCase (unquote_case_info a,unquote_predicate b,c,List.map unquote_branch d)
    | Coq_tProj (a,b) -> ACoq_tProj (a,b)
    | Coq_tFix (a,b) -> ACoq_tFix (List.map unquote_def a,b)
    | Coq_tCoFix (a,b) -> ACoq_tCoFix (List.map unquote_def a,b)
    | Coq_tInt i -> ACoq_tInt i
    | Coq_tFloat f -> ACoq_tFloat f
    | Coq_tString s -> ACoq_tString s
    | Coq_tArray (u, arr, def, ty) -> ACoq_tArray (u, Array.of_list arr, def, ty)

  let unquote_string = Caml_bytestring.caml_string_of_bytestring

  let unquote_ident (qi: quoted_ident) : Id.t =
    let s = unquote_string qi in
    Id.of_string s

  let unquote_relevance (r : relevance) : Sorts.relevance =
    match r with
    | BasicAst.Relevant -> Sorts.Relevant
    | BasicAst.Irrelevant -> Sorts.Irrelevant

  let unquote_name (q: quoted_name) : Name.t =
    match q with
    | Coq_nAnon -> Anonymous
    | Coq_nNamed n -> Name (unquote_ident n)

  let unquote_aname (q: quoted_aname) : Name.t Constr.binder_annot =
    {Context.binder_name = unquote_name q.binder_name;
     Context.binder_relevance = unquote_relevance q.binder_relevance}

  let unquote_int (q: quoted_int) : int = Caml_nat.caml_int_of_nat q

  let unquote_evar env evm n l =
    let id = Evar.unsafe_of_int (unquote_int n) in
    evm, mkEvar (id, SList.of_full_list l)

  let unquote_bool (q : quoted_bool) : bool = q

  let unquote_hint_locality (l : quoted_hint_locality) : Hints.hint_locality = l

  let unquote_int63 i = i

  let unquote_float64 i = i

  let unquote_pstring s = s

  (* val unquote_sort : quoted_sort -> Sorts.t *)
  (* val unquote_sort_family : quoted_sort_family -> Sorts.family *)
  let unquote_cast_kind (q : quoted_cast_kind) : Constr.cast_kind =
    match q with
    | VmCast -> VMcast
    | NativeCast -> NATIVEcast
    | Cast -> DEFAULTcast

  let unquote_dirpath dp : DirPath.t =
    let l = List.map unquote_ident dp in
    DirPath.make l

  let rec unquote_modpath mp : ModPath.t =
    match mp with
    | MPfile dp -> MPfile (unquote_dirpath dp)
    | MPbound (dp, id, i) ->
      MPbound (Obj.magic (unquote_int i, unquote_ident id, unquote_dirpath dp) : MBId.t)
    | MPdot (mp, id) -> MPdot (unquote_modpath mp, Label.of_id (unquote_ident id))

  let unquote_kn ((mp, id) : quoted_kernel_name) : KerName.t =
    KerName.make (unquote_modpath mp) (Label.of_id (unquote_ident id))

  let unquote_inductive (q: quoted_inductive) : Names.inductive =
    let { inductive_mind = kn; inductive_ind = i } = q in
    (MutInd.make1 (unquote_kn kn), unquote_int i)

  (*val unquote_univ_instance :  quoted_univ_instance -> UVars.Instance.t *)
  let unquote_proj (q : quoted_proj) : (quoted_inductive * quoted_int * quoted_int) =
    let { proj_ind = ind; proj_npars = ps; proj_arg = idx } = q in
    (ind, ps, idx)

  let unquote_level (trm : Universes0.Level.t) : Univ.Level.t =
    match trm with
    | Universes0.Level.Coq_lzero -> Univ.Level.set
    | Universes0.Level.Coq_level s ->
      let s = unquote_string s in
      let comps = CString.split_on_char '.' s in
      let last, dp = CList.sep_last comps in
      let dp = DirPath.make (List.map Id.of_string comps) in
      let idx = int_of_string last in
      (* TODO handle universes from workers *)
      Univ.Level.make (Univ.UGlobal.make dp "" idx)
    | Universes0.Level.Coq_lvar n -> Univ.Level.var (unquote_int n)

  let unquote_level_expr (trm : Universes0.Level.t * quoted_int) : Univ.Universe.t =
    let l = unquote_level (fst trm) in
    let u = Univ.Universe.make l in
    Caml_nat.iter_nat Univ.Universe.super u (snd trm)

  let unquote_universe evm (trm : Universes0.Universe.t) =
    let u = Universes0.t_set trm in
    let ux_list = Universes0.LevelExprSet.elements u in
    let l = List.map unquote_level_expr ux_list in
    let u = List.fold_left Univ.Universe.sup (List.hd l) (List.tl l) in
    evm, u

  let unquote_sort evm trm =
    match trm with
    | Universes0.Sort.Coq_sSProp -> evm, Sorts.sprop
    | Universes0.Sort.Coq_sProp -> evm, Sorts.prop
    | Universes0.Sort.Coq_sType u ->
      let evm, u = unquote_universe evm u in
      evm, Sorts.sort_of_univ u

  let unquote_universe_level evm l = evm, unquote_level l

  let unquote_universe_instance(evm: Evd.evar_map) (l: quoted_univ_instance): Evd.evar_map * UVars.Instance.t
  = (evm,  UVars.Instance.of_array ([||], Array.of_list (List.map unquote_level l)))


  let unquote_global_reference (trm : Kernames.global_reference) : GlobRef.t =
    let open GlobRef in
    match trm with
    | VarRef id -> VarRef (unquote_ident id)
    | ConstRef kn -> ConstRef (Constant.make1 (unquote_kn kn))
    | IndRef ind -> IndRef (unquote_inductive ind)
    | ConstructRef (ind, k) -> ConstructRef (unquote_inductive ind, unquote_int k)


end

module ExtractionDenoter = Denoter.Denoter(BaseExtractionDenoter)


include BaseExtractionDenoter
include ExtractionDenoter
