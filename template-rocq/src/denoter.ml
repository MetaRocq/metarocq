open Names
open Tm_util
open Reification

module type BaseDenoter =
sig
  include Reification

  val unquote_ident : quoted_ident -> Id.t
  val unquote_name : quoted_name -> Name.t
  val unquote_aname : quoted_aname -> Name.t Constr.binder_annot
  val unquote_relevance : quoted_relevance -> Sorts.relevance
  val unquote_evar : Environ.env -> Evd.evar_map -> quoted_int -> Constr.t list -> Evd.evar_map * Constr.t
  val unquote_int : quoted_int -> int
  val unquote_bool : quoted_bool -> bool
  val unquote_int63 : quoted_int63 -> Uint63.t
  val unquote_float64 : quoted_float64 -> Float64.t
  val unquote_pstring : quoted_pstring -> Pstring.t
  val unquote_cast_kind : quoted_cast_kind -> Constr.cast_kind
  val unquote_kn :  quoted_kernel_name -> KerName.t
  val unquote_inductive :  quoted_inductive -> Names.inductive
  (*val unquote_univ_instance :  quoted_univ_instance -> UVars.Instance.t *)
  val unquote_proj : quoted_proj -> (quoted_inductive * quoted_int * quoted_int)
  (* val unquote_universe : Evd.evar_map -> quoted_universe -> Evd.evar_map * Univ.Universe.t *)
  val unquote_universe_level : Evd.evar_map -> quoted_univ_level -> Evd.evar_map * Univ.Level.t
  val unquote_universe_instance: Evd.evar_map -> quoted_univ_instance -> Evd.evar_map * UVars.Instance.t
  val unquote_sort : Evd.evar_map -> quoted_sort -> Evd.evar_map * Sorts.t
  (* val unquote_sort_family : quoted_sort_family -> Sorts.family *)
  (* val representsIndConstuctor : quoted_inductive -> Term.constr -> bool *)
  val inspect_term : t -> (t, quoted_int, quoted_ident, quoted_aname, quoted_sort, quoted_cast_kind,
    quoted_kernel_name, quoted_inductive, quoted_relevance, quoted_univ_level, quoted_univ_instance, quoted_proj,
    quoted_int63, quoted_float64, quoted_pstring) structure_of_term

end


(* todo: the recursive call is uneeded provided we call it on well formed terms *)

let strict_unquote_universe_mode = ref true


let map_evm (f : 'a -> 'b -> 'a * 'c) (evm : 'a) (l : 'b list) : 'a * ('c list) =
  let evm, res = List.fold_left (fun (evm, l) b -> let evm, c = f evm b in evm, c :: l) (evm, []) l in
  evm, List.rev res

let array_map_evm (f : 'a -> 'b -> 'a * 'c) (evm : 'a) (l : 'b array) : 'a * ('c array) =
  CArray.fold_left_map (fun evm b -> let evm, c = f evm b in evm, c) evm l

let fold_env_evm_right (f : 'a -> 'b -> 'c -> 'a * 'b * 'd) (env : 'a) (evm : 'b) (l : 'c list) : 'a * 'b * ('d list) =
  List.fold_right (fun b (env, evm, l) -> let env, evm, c = f env evm b in env, evm, c :: l) l (env, evm, [])

module Denoter (D : BaseDenoter) =
struct

  (* TODO: replace app_full by this abstract version?*)
  let rec app_full_abs (trm: D.t) (acc: D.t list) =
    match D.inspect_term trm with
      ACoq_tApp (f, xs) -> app_full_abs f (xs @ acc)
    | _ -> (trm, acc)

  let push_rec_types (lna,typarray) env =
    let open Context.Rel.Declaration in
    let ctxt = CArray.map2_i (fun i na t -> LocalAssum (na, Vars.lift i t)) lna typarray in
    Array.fold_left (fun e assum -> Environ.push_rel assum e) env ctxt

  let denote_term (env : Environ.env) (evm : Evd.evar_map) (trm: D.t) : Evd.evar_map * Constr.t =
    let open Context.Rel.Declaration in
    let rec aux env evm (trm: D.t) : _ * Constr.t =
      (* debug (fun () -> Pp.(str "denote_term" ++ spc () ++ Printer.pr_econstr_env env evm trm)) ;  *)
      match D.inspect_term trm with
      | ACoq_tRel x -> evm, Constr.mkRel (D.unquote_int x + 1)
      | ACoq_tVar x -> evm, Constr.mkVar (D.unquote_ident x)
      | ACoq_tEvar (n, l) ->
        let evm, l' = map_evm (aux env) evm l in
        D.unquote_evar env evm n l'
      | ACoq_tSort x -> let evm, s = D.unquote_sort evm x in evm, Constr.mkSort s
      | ACoq_tCast (t,c,ty) -> let evm, t = aux env evm t in
        let evm, ty = aux env evm ty in
        evm, Constr.mkCast (t, D.unquote_cast_kind c, ty)
      | ACoq_tProd (n,t,b) -> let evm, t = aux env evm t in
        let n = D.unquote_aname n in
        let evm, b = aux (Environ.push_rel (LocalAssum (n, t)) env) evm b in
        evm, Constr.mkProd (n, t, b)
      | ACoq_tLambda (n,t,b) ->
        let n = D.unquote_aname n in
        let evm, t = aux env evm t in
        let evm, b = aux (Environ.push_rel (LocalAssum (n, t)) env) evm b in
        evm, Constr.mkLambda (n, t, b)
      | ACoq_tLetIn (n,e,t,b) ->
        let n = D.unquote_aname n in
        let evm, e = aux env evm e in
        let evm, t = aux env evm t in
        let evm, b = aux (Environ.push_rel (LocalDef (n, e, t)) env) evm b in
        evm, Constr.mkLetIn (n, e, t, b)
      | ACoq_tApp (f,xs) -> let evm, f = aux env evm f in
        let evm, xs = map_evm (aux env) evm xs in
        evm, Constr.mkApp (f, Array.of_list xs)
      | ACoq_tConst (s,u) ->
        let s = D.unquote_kn s in
        let evm, u = D.unquote_universe_instance evm u in
        (* XXX use the Environ API when available *)
        let cst = Global.constant_of_delta_kn s in
        evm, Constr.mkConstU (cst, u)
      | ACoq_tConstruct (i,idx,u) ->
        let ind = D.unquote_inductive i in
        let evm, u = D.unquote_universe_instance evm u in
        evm, Constr.mkConstructU ((ind, D.unquote_int idx + 1), u)
      | ACoq_tInd (i, u) ->
        let i = D.unquote_inductive i in
        let evm, u = D.unquote_universe_instance evm u in
        evm, Constr.mkIndU (i, u)
      | ACoq_tCase (ci, p, c, brs) ->
        let ind = D.unquote_inductive ci.aci_ind in
        let relevance = D.unquote_relevance ci.aci_relevance in
        let ci = Inductiveops.make_case_info (Global.env ()) ind Constr.RegularStyle in
        let evm, puinst = D.unquote_universe_instance evm p.auinst in
        let evm, pars = map_evm (aux env) evm p.apars in
        let pars = Array.of_list pars in
        let napctx = CArray.map_of_list D.unquote_aname (List.rev p.apcontext) in
        let pctx = CaseCompat.case_predicate_context env ci puinst pars napctx in
        let evm, pret = aux (Environ.push_rel_context pctx env) evm p.apreturn in
        let evm, c = aux env evm c in
        let brs = List.map (fun { abcontext = bctx; abbody = bbody } ->
          let nabctx = CArray.map_of_list D.unquote_aname (List.rev bctx) in
          (nabctx, bbody)) brs in
        let brs = CaseCompat.case_branches_contexts env ci puinst pars (Array.of_list brs) in
        let denote_br evm (nas, bctx, bbody) =
          let evm, bbody = aux (Environ.push_rel_context bctx env) evm bbody in
          evm, (nas, bbody)
        in
        let evm, brs = array_map_evm denote_br evm brs in
        (* todo: reify better case_info *)
        let pcase = (ci, puinst, pars, ((napctx, pret), relevance), Constr.NoInvert, c, brs) in
        evm, Constr.mkCase pcase
      | ACoq_tFix (lbd, i) ->
        let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
                                          List.map (fun p->p.rarg) lbd) in
        let evm, types = map_evm (aux env) evm types in
        let (names,rargs) = (List.map D.unquote_aname names, List.map D.unquote_int rargs) in
        let la = Array.of_list in
        let lnames = la names and ltypes = la types in
        let env = push_rec_types (lnames, ltypes) env in
        let evm, bodies = map_evm (aux env) evm bodies in
        evm, Constr.mkFix ((la rargs, D.unquote_int i), (lnames, ltypes, la bodies))
      | ACoq_tCoFix (lbd, i) ->
        let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
                                          List.map (fun p->p.rarg) lbd) in
        let evm, types = map_evm (aux env) evm types in
        let (names,rargs) = (List.map D.unquote_aname names, List.map D.unquote_int rargs) in
        let la = Array.of_list in
        let lnames = la names and ltypes = la types in
        let env = push_rec_types (lnames, ltypes) env in
        let evm, bodies = map_evm (aux env) evm bodies in
        evm, Constr.mkCoFix (D.unquote_int i, (lnames, ltypes, la bodies))

      | ACoq_tProj (proj,t) ->
         let (ind, _npars, arg) = D.unquote_proj proj in
         let ind' = D.unquote_inductive ind in
         let proj_arg = D.unquote_int arg in
         let mib = Environ.lookup_mind (fst ind') env in
         let p', r = Declareops.inductive_make_projection ind' mib ~proj_arg in
         let p' = Names.Projection.make p' false in
         let evm, t' = aux env evm t in
         let r = match r with
           | Relevant | Irrelevant -> r
           | RelevanceVar _ -> CErrors.user_err Pp.(str "Unquoting sort poly projections not yet supported.")
         in
         evm, Constr.mkProj (p', r, t')
      | ACoq_tInt x -> evm, Constr.mkInt (D.unquote_int63 x)
      | ACoq_tFloat x -> evm, Constr.mkFloat (D.unquote_float64 x)
      | ACoq_tString x -> evm, Constr.mkString (D.unquote_pstring x)
      | ACoq_tArray (u, arr, def, ty) ->
          let evm, u = D.unquote_universe_level evm u in
          let evm, arr = CArray.fold_left_map (fun evm a -> aux env evm a) evm arr in
          let evm, def = aux env evm def in
          let evm, ty = aux env evm ty in
          evm, Constr.mkArray (UVars.Instance.of_array ([||], [|u|]), arr, def, ty)

    in aux env evm trm

end
