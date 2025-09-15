open Names
open Entries
open Declarations
open Pp

open Tm_util
open Reification

let inductive_sort mip = mip.mind_sort

let cast_prop = ref (false)

(* whether Set Template Cast Propositions is on, as needed for erasure in Certicoq *)
let is_cast_prop () = !cast_prop

let metarocq_cat = match CWarnings.get_category "metarocq" with
  | There c -> c
  | OtherType -> assert false
  | NotThere -> CWarnings.create_category ~name:"metarocq" ()

let make_warning_if_not_exist w =
  match CWarnings.get_warning w with
  | There w -> w
  | OtherType -> assert false (* used as category *)
  | NotThere -> CWarnings.create_warning ~name:w ~from:[metarocq_cat] ()

let warn_primitive_turned_into_axiom =
  CWarnings.create_in (make_warning_if_not_exist "primitive-turned-into-axiom")
          Pp.(fun prim -> str "Quoting primitive " ++ str prim ++ str " into an axiom.")

let warn_symbol_turned_into_axiom =
  CWarnings.create_in (make_warning_if_not_exist "symbol-turned-into-axiom")
          Pp.(fun prim -> str "Quoting symbol " ++ str prim ++ str " into an axiom.")
let warn_ignoring_private_polymorphic_universes =
  CWarnings.create_in (make_warning_if_not_exist "private-polymorphic-universes-ignored")
          Pp.(fun () -> str "Ignoring private polymorphic universes.")

let toDecl (old: Name.t Constr.binder_annot * ((Constr.constr) option) * Constr.constr) : Constr.rel_declaration =
  let (name,value,typ) = old in
  match value with
  | Some value -> Context.Rel.Declaration.LocalDef (name,value,typ)
  | None -> Context.Rel.Declaration.LocalAssum (name,typ)

let getType env (t:Constr.t) : Constr.t =
    EConstr.to_constr Evd.empty (Retyping.get_type_of env Evd.empty (EConstr.of_constr t))

let hnf_type env ty =
  let rec hnf_type continue ty =
    match Constr.kind ty with
      Constr.Prod (n,t,b) -> Constr.mkProd (n,t,hnf_type true b)
    | Constr.LetIn _
      | Constr.Cast _
      | Constr.App _ when continue ->
       hnf_type false (Reduction.whd_all env ty)
    | _ -> ty
  in
  hnf_type true ty



module type BaseQuoter =
sig
  include Reification

  val mkRel : quoted_int -> t
  val mkVar : quoted_ident -> t
  val mkEvar : quoted_int -> t array -> t
  val mkSort : quoted_sort -> t
  val mkCast : t -> quoted_cast_kind -> t -> t
  val mkProd : quoted_aname -> t -> t -> t
  val mkLambda : quoted_aname -> t -> t -> t
  val mkLetIn : quoted_aname -> t -> t -> t -> t
  val mkApp : t -> t array -> t
  val mkConst : quoted_kernel_name -> quoted_univ_instance -> t
  val mkInd : quoted_inductive -> quoted_univ_instance -> t
  val mkConstruct : quoted_inductive * quoted_int -> quoted_univ_instance -> t
  val mkCase : (quoted_inductive * quoted_int * quoted_relevance) ->
    (quoted_univ_instance * t array * quoted_aname array * t) -> (* predicate: instance, params, binder names, return type *)
     t -> (quoted_aname array * t) list (* branches *) -> t
  val mkProj : quoted_proj -> t -> t
  val mkFix : (quoted_int array * quoted_int) * (quoted_aname array * t array * t array) -> t
  val mkCoFix : (quoted_int array * quoted_int) * (quoted_aname array * t array * t array) -> t
  val mkInt : quoted_int63 -> t
  val mkFloat : quoted_float64 -> t
  val mkString : quoted_pstring -> t
  val mkArray : quoted_univ_level -> t array -> default:t -> ty:t -> t

  val mkBindAnn : quoted_name -> quoted_relevance -> quoted_aname
  val mkName : quoted_ident -> quoted_name
  val mkAnon : unit -> quoted_name

  val quote_ident : Id.t -> quoted_ident
  val quote_name : Name.t -> quoted_name
  val quote_aname : Name.t Constr.binder_annot -> quoted_aname
  val quote_relevance : Sorts.relevance -> quoted_relevance
  val quote_int : int -> quoted_int
  val quote_bool : bool -> quoted_bool
  val quote_sort : Sorts.t -> quoted_sort
  val quote_sort_quality_or_set : UnivGen.QualityOrSet.t -> quoted_sort_quality_or_set
  val quote_cast_kind : Constr.cast_kind -> quoted_cast_kind
  val quote_kn : KerName.t -> quoted_kernel_name
  val quote_inductive : quoted_kernel_name * quoted_int -> quoted_inductive
  val quote_proj : quoted_inductive -> quoted_int -> quoted_int -> quoted_proj

  (* Primitive objects *)
  val quote_int63 : Uint63.t -> quoted_int63
  val quote_float64 : Float64.t -> quoted_float64
  val quote_pstring : Pstring.t -> quoted_pstring

  val quote_constraint_type : Univ.constraint_type -> quoted_constraint_type
  val quote_univ_constraint : Univ.univ_constraint -> quoted_univ_constraint
  val quote_univ_level : Univ.Level.t -> quoted_univ_level
  val quote_univ_instance : UVars.Instance.t -> quoted_univ_instance
  val quote_univ_constraints : Univ.Constraints.t -> quoted_univ_constraints
  val quote_univ_context : UVars.UContext.t -> quoted_univ_context
  val quote_univ_contextset : Univ.ContextSet.t -> quoted_univ_contextset
  val quote_variance : UVars.Variance.t -> quoted_variance
  val quote_abstract_univ_context : UVars.AbstractContext.t -> quoted_abstract_univ_context

  val mkMonomorphic_entry : quoted_univ_contextset -> quoted_universes_entry
  val mkPolymorphic_entry : quoted_univ_context -> quoted_universes_entry

  val mkMonomorphic_ctx : unit -> quoted_universes_decl
  val mkPolymorphic_ctx : quoted_abstract_univ_context -> quoted_universes_decl

  val quote_mind_finiteness : Declarations.recursivity_kind -> quoted_mind_finiteness
  val quote_mutual_inductive_entry :
    quoted_mind_finiteness * quoted_context (* params *) * quoted_ind_entry list *
    quoted_universes_entry * quoted_variance option list option ->
    quoted_mind_entry

  val quote_definition_entry : t option -> t -> quoted_universes_entry -> quoted_definition_entry
  val quote_parameter_entry : t -> quoted_universes_entry -> quoted_parameter_entry
  val quote_constant_entry : (quoted_definition_entry, quoted_parameter_entry) sum -> quoted_constant_entry

  (* val quote_entry : (quoted_constant_entry, quoted_mind_entry) sum option > quoted_entry *)

  val quote_context_decl : quoted_aname -> t option -> t -> quoted_context_decl
  val quote_context : quoted_context_decl list -> quoted_context

  val mk_one_inductive_body :
    quoted_ident *
    quoted_context (* ind indices context *) *
    quoted_sort (* ind sort *) *
    t (* ind type *) *
    quoted_sort_quality_or_set *
    (quoted_ident * quoted_context (* arguments context *) *
      t list (* indices in the conclusion *) *
      t (* constr type *) *
      quoted_int (* arity (w/o lets) *)) list *
    (quoted_ident * quoted_relevance *  t (* projection type *)) list *
    quoted_relevance ->
    quoted_one_inductive_body

  val mk_mutual_inductive_body :
    quoted_mind_finiteness
    -> quoted_int (* number of params (no lets) *)
    -> quoted_context (* parameters context with lets *)
    -> quoted_one_inductive_body list
    -> quoted_universes_decl
    -> quoted_variance list option
    -> quoted_mutual_inductive_body

  val mk_constant_body : t (* type *) -> t option (* body *) -> quoted_universes_decl -> quoted_relevance -> quoted_constant_body

  val mk_inductive_decl : quoted_mutual_inductive_body -> quoted_global_decl

  val mk_constant_decl : quoted_constant_body -> quoted_global_decl

  val empty_global_declarations : unit -> quoted_global_declarations
  val add_global_decl : quoted_kernel_name -> quoted_global_decl -> quoted_global_declarations -> quoted_global_declarations

  type pre_quoted_retroknowledge =
    { retro_int63 : quoted_kernel_name option;
      retro_float64 : quoted_kernel_name option;
      retro_string : quoted_kernel_name option;
      retro_array : quoted_kernel_name option }

  val quote_retroknowledge : pre_quoted_retroknowledge -> quoted_retroknowledge

  val mk_global_env : quoted_univ_contextset -> quoted_global_declarations -> quoted_retroknowledge -> quoted_global_env
  val mk_program : quoted_global_env -> t -> quoted_program
end



module Quoter (Q : BaseQuoter) =
struct

  let push_rel decl (in_prop, env) = (in_prop, Environ.push_rel decl env)
  let push_rel_context ctx (in_prop, env) = (in_prop, Environ.push_rel_context ctx env)

  let get_abstract_inductive_universes iu =
    match iu with
    | Declarations.Monomorphic -> UVars.UContext.empty
    | Polymorphic ctx -> UVars.AbstractContext.repr ctx

  let quote_universes_entry = function
    | Monomorphic_entry -> Q.mkMonomorphic_entry (Q.quote_univ_contextset Univ.ContextSet.empty)
    | Polymorphic_entry ctx -> Q.mkPolymorphic_entry (Q.quote_univ_context ctx)

  let quote_universes_decl decl templ =
    match decl with
    | Monomorphic -> Q.mkMonomorphic_ctx ()
    | Polymorphic ctx -> Q.mkPolymorphic_ctx (Q.quote_abstract_univ_context ctx)

  let quote_ugraph ?kept (g : UGraph.t) =
    debug Pp.(fun () -> str"Quoting ugraph");
    let levels, cstrs, eqs =
      match kept with
      | None ->
        let cstrs, eqs = UGraph.constraints_of_universes g in
        UGraph.domain g, cstrs, eqs
      | Some l ->
        debug Pp.(fun () -> str"Quoting graph restricted to: " ++ Univ.Level.Set.pr Univ.Level.raw_pr l);
        (* Feedback.msg_debug Pp.(str"Graph is: "  ++ UGraph.pr_universes Univ.Level.raw_pr (UGraph.repr g)); *)
        let dom = UGraph.domain g in
        let kept = Univ.Level.Set.inter dom l in
        let kept = Univ.Level.Set.remove Univ.Level.set kept in
        let cstrs = time Pp.(str"Computing graph restriction") (UGraph.constraints_for ~kept) g in
        l, cstrs, []
    in
    let levels, cstrs =
      List.fold_right (fun eqs acc ->
        match Univ.Level.Set.elements eqs with
        | [] -> acc
        | x :: [] -> acc
        | x :: rest ->
          List.fold_right (fun p (levels, cstrs) ->
            (Univ.Level.Set.add p levels, Univ.Constraints.add (x, Univ.Eq, p) cstrs)) rest acc)
        eqs (levels, cstrs)
    in
    let levels = Univ.Level.Set.add Univ.Level.set levels in
    debug Pp.(fun () -> str"Universe context: " ++ Univ.ContextSet.pr Univ.Level.raw_pr (levels, cstrs));
    time (Pp.str"Quoting universe context")
      (fun uctx -> Q.quote_univ_contextset uctx) (levels, cstrs)

  let quote_inductive' (ind, i) : Q.quoted_inductive =
    Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical ind), Q.quote_int i)

  let quote_rel_decl quote_term acc env sigma = function
      | Context.Rel.Declaration.LocalAssum (na, t) ->
        let t', acc = quote_term acc env sigma t in
        (Q.quote_context_decl (Q.quote_aname na) None t', acc)
      | Context.Rel.Declaration.LocalDef (na, b, t) ->
        let b', acc = quote_term acc env sigma b in
        let t', acc = quote_term acc env sigma t in
        (Q.quote_context_decl (Q.quote_aname na) (Some b') t', acc)

  let quote_rel_context quote_term acc env sigma ctx =
      let decls, env, acc =
        List.fold_right (fun decl (ds, env, acc) ->
            let x, acc = quote_rel_decl quote_term acc env sigma decl in
            (x :: ds, push_rel decl env, acc))
          ctx ([],env,acc) in
      Q.quote_context decls, acc

  let quote_binder b =
    Q.quote_aname b

  let quote_name_annots nas =
    Array.map quote_binder nas

  let quote_terms quote_term acc env sigma ts =
    let acc, ts =
      CArray.fold_left_map (fun acc t -> let (x, acc) = quote_term acc env sigma t in acc, x) acc ts
    in ts, acc

  let cofixpoint_arities ts =
    let cofix_arity t =
      let ctx, _concl = Term.decompose_prod_decls t in
      Context.Rel.nhyps ctx
    in Array.map cofix_arity ts

  let quote_term_remember
      (add_constant : KerName.t -> 'a -> 'a)
      (add_inductive : Names.inductive -> Declarations.mutual_inductive_body -> 'a -> 'a) =
    let rec quote_term (acc : 'a) env sigma trm =
      let aux acc env trm =
      match Constr.kind trm with
      | Constr.Rel i -> (Q.mkRel (Q.quote_int (i - 1)), acc)
      | Constr.Var v -> (Q.mkVar (Q.quote_ident v), acc)
      | Constr.Evar (n,args) ->
        let args = Evd.expand_existential0 sigma (n, args) in
	      let (args',acc) = quote_terms quote_term acc env sigma (Array.of_list args) in
         (Q.mkEvar (Q.quote_int (Evar.repr n)) args', acc)
      | Constr.Sort s -> (Q.mkSort (Q.quote_sort s), acc)
      | Constr.Cast (c,k,t) ->
              let (c',acc) = quote_term acc env sigma c in
              let (t',acc) = quote_term acc env sigma t in
        let k' = Q.quote_cast_kind k in
        (Q.mkCast c' k' t', acc)

      | Constr.Prod (n,t,b) ->
              let (t',acc) = quote_term acc env sigma t in
        let env = push_rel (toDecl (n, None, t)) env in
        let (b',acc) = quote_term acc env sigma b in
        (Q.mkProd (Q.quote_aname n) t' b', acc)

      | Constr.Lambda (n,t,b) ->
	      let (t',acc) = quote_term acc env sigma t in
              let (b',acc) = quote_term acc (push_rel (toDecl (n, None, t)) env) sigma b in
        (Q.mkLambda (Q.quote_aname n) t' b', acc)

      | Constr.LetIn (n,e,t,b) ->
	      let (e',acc) = quote_term acc env sigma e in
	      let (t',acc) = quote_term acc env sigma t in
	      let (b',acc) = quote_term acc (push_rel (toDecl (n, Some e, t)) env) sigma b in
      	(Q.mkLetIn (Q.quote_aname n) e' t' b', acc)

      | Constr.App (f,xs) ->
        let (f',acc) = quote_term acc env sigma f in
        let (xs',acc) = quote_terms quote_term acc env sigma xs in
        (Q.mkApp f' xs', acc)

      | Constr.Const (c,pu) ->
        let kn = Constant.canonical c in
        (Q.mkConst (Q.quote_kn kn) (Q.quote_univ_instance pu), add_constant kn acc)

      | Constr.Construct ((mind,c),pu) ->
        let mib = Environ.lookup_mind (fst mind) (snd env) in
         (Q.mkConstruct (quote_inductive' mind, Q.quote_int (c - 1)) (Q.quote_univ_instance pu),
          add_inductive mind mib acc)

      | Constr.Ind (mind,pu) ->
         (Q.mkInd (quote_inductive' mind) (Q.quote_univ_instance pu),
          let mib = Environ.lookup_mind (fst mind) (snd env) in
          add_inductive mind mib acc)

      | Constr.Case (ci,u,pars, ((predctx, pred), relevance), iv, discr, brs) ->
        let ind = Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical (fst ci.Constr.ci_ind)),
                                      Q.quote_int (snd ci.Constr.ci_ind)) in
        let npar = Q.quote_int ci.Constr.ci_npar in
        let q_relevance = Q.quote_relevance relevance in
        let acc, q_pars = CArray.fold_left_map (fun acc par -> let (qt, acc) = quote_term acc env sigma par in acc, qt) acc pars in
        let qu = Q.quote_univ_instance u in
        let pctx = CaseCompat.case_predicate_context (snd env) ci u pars predctx in
        let qpctx = quote_name_annots predctx in
        let (qpred,acc) = quote_term acc (push_rel_context pctx env) sigma pred in
        let (qdiscr,acc) = quote_term acc env sigma discr in
        let cbrs = CaseCompat.case_branches_contexts (snd env) ci u pars brs in
        let (branches,acc) =
          CArray.fold_left2 (fun (bodies,acc) (brnas, brctx, bbody) narg ->
            let (qbody,acc) = quote_term acc (push_rel_context brctx env) sigma bbody in
            let qctx = quote_name_annots brnas in
              ((qctx, qbody) :: bodies, acc))
          ([],acc) cbrs ci.Constr.ci_cstr_nargs in
        (Q.mkCase (ind, npar, q_relevance) (qu, q_pars, qpctx, qpred) qdiscr (List.rev branches), acc)

      | Constr.Fix fp -> quote_fixpoint acc env sigma fp
      | Constr.CoFix fp -> quote_cofixpoint acc env sigma fp
      | Constr.Proj (p,_,c) ->
         let ind = quote_inductive' (Projection.inductive p) in
         let pars = Q.quote_int (Projection.npars p) in
         let arg  = Q.quote_int (Projection.arg p)   in
         let p' = Q.quote_proj ind pars arg in
         let t', acc = quote_term acc env sigma c in
         let mib = Environ.lookup_mind (fst (Projection.inductive p)) (snd env) in
         (Q.mkProj p' t', add_inductive (Projection.inductive p) mib acc)
      | Constr.Int i -> (Q.mkInt (Q.quote_int63 i), acc)
      | Constr.Float f -> (Q.mkFloat (Q.quote_float64 f), acc)
      | Constr.String s -> (Q.mkString (Q.quote_pstring s), acc)
      | Constr.Meta _ -> failwith "Meta not supported by TemplateRocq"
      | Constr.Array (u, ar, def, ty) ->
        let u = match UVars.Instance.to_array u with (_, [| u |]) -> u | _ -> assert false in
        let def', acc = quote_term acc env sigma def in
        let ty', acc = quote_term acc env sigma ty in
        let acc, arr' = CArray.fold_left_map (fun acc t -> let t', acc = quote_term acc env sigma t in acc, t') acc ar in
        Q.mkArray (Q.quote_univ_level u) arr' ~default:def' ~ty:ty', acc
      in
      aux acc env trm
    and quote_recdecl (acc : 'a) env sigma b (ns,ts,ds) =
      let ctxt =
        CArray.map2_i (fun i na t -> (Context.Rel.Declaration.LocalAssum (na, Vars.lift i t))) ns ts in
      let envfix = push_rel_context (CArray.rev_to_list ctxt) env in
      let ns' = Array.map quote_binder ns in
      let b' = Q.quote_int b in
      let ts', acc = quote_terms quote_term acc env sigma ts in
      let ds', acc = quote_terms quote_term acc envfix sigma ds in
      ((b',(ns',ts',ds')), acc)
    and quote_fixpoint acc env sigma ((a,b),decl) =
      let a' = Array.map Q.quote_int a in
      let (b',decl'),acc = quote_recdecl acc env sigma b decl in
      (Q.mkFix ((a',b'),decl'), acc)
    and quote_cofixpoint acc env sigma (a,(_, ts, _ as decl)) =
      let arities = cofixpoint_arities ts in
      let qarities = Array.map Q.quote_int arities in
      let (a',decl'),acc = quote_recdecl acc env sigma a decl in
      (Q.mkCoFix ((qarities,a'),decl'), acc)
    and quote_minductive_type (acc : 'a) env sigma (t : MutInd.t) mib =
      let uctx = get_abstract_inductive_universes mib.Declarations.mind_universes in
      let inst = UVars.UContext.instance uctx in
      let indtys =
        (CArray.map_to_list (fun oib ->
           let ty = Inductive.type_of_inductive ((mib,oib),inst) in
           (Context.Rel.Declaration.LocalAssum (Context.annotR (Names.Name oib.mind_typename), ty))) mib.mind_packets)
      in
      let envind = push_rel_context (List.rev indtys) env in
      let ref_name = Q.quote_kn (MutInd.canonical t) in
      let ntyps = Array.length mib.mind_packets in
      let (ls,acc) =
        List.fold_left (fun (ls,acc) oib ->
          let named_ctors =
            CList.combine3
              (Array.to_list oib.mind_consnames)
              (Array.to_list oib.mind_nf_lc)
              (Array.to_list oib.mind_consnrealargs)
          in
          let indty = Inductive.type_of_inductive ((mib,oib),inst) in
          let indices, pars =
            let ctx = oib.mind_arity_ctxt in
            CList.chop (List.length ctx - List.length mib.mind_params_ctxt) ctx
          in
          let indices, acc = quote_rel_context quote_term acc (push_rel_context pars env) sigma indices in
          let indty, acc = quote_term acc env sigma indty in
          let indsort = Q.quote_sort (inductive_sort oib) in
          let (reified_ctors,acc) =
            List.fold_left (fun (ls,acc) (nm,(ctx, ty),ar) ->
              let ty = Term.it_mkProd_or_LetIn ty ctx in
              let ty = Inductive.abstract_constructor_type_relatively_to_inductive_types_context ntyps t ty in
              let ctx, concl = Term.decompose_prod_decls ty in
              let argctx, parsctx =
                CList.chop (List.length ctx - List.length mib.mind_params_ctxt) ctx
              in
              let envcstr = push_rel_context parsctx envind in
              let qargctx, acc = quote_rel_context quote_term acc envcstr sigma argctx in
              let qindices, acc =
                let hd, args = Constr.decompose_app concl in
                let pars, args = CArray.chop mib.mind_nparams args in
                let envconcl = push_rel_context argctx envcstr in
                quote_terms quote_term acc envconcl sigma args
              in
              let (ty,acc) = quote_term acc envind sigma ty in
              ((Q.quote_ident nm, qargctx, Array.to_list qindices, ty, Q.quote_int ar) :: ls, acc))
              ([],acc) named_ctors
          in
          let projs, acc =
            match mib.Declarations.mind_packets with
            (* TODO handle mutual records *)
            | [| { mind_record = PrimRecord (id, csts, relevance, ps) } |] ->
                let ctxwolet = Vars.smash_rel_context mib.mind_params_ctxt in
                let indty = Constr.mkApp (Constr.mkIndU ((t,0),inst),
                                        Context.Rel.instance Constr.mkRel 0 ctxwolet) in
                let indbinder = Context.Rel.Declaration.LocalAssum (Context.annotR (Names.Name id),indty) in
                let envpars = push_rel_context (indbinder :: ctxwolet) env in
                let ps, acc = CArray.fold_right3 (fun cst pb rel (ls,acc) ->
                  let (ty, acc) = quote_term acc envpars sigma pb in
                  let na = Q.quote_ident (Names.Label.to_id cst) in
                  let rel = Q.quote_relevance rel in
                  ((na, rel, ty) :: ls, acc)) csts ps relevance ([],acc)
                in ps, acc
            | _ -> [], acc
          in
          (* TODO quote the real squash data instead of approximating with a quality or set *)
          let kelim = match oib.Declarations.mind_squashed with
            | None -> UnivGen.QualityOrSet.qtype
            | Some _ -> UnivGen.QualityOrSet.of_sort oib.mind_sort
          in
          let sf = Q.quote_sort_quality_or_set kelim in
            (Q.quote_ident oib.mind_typename, indices, indsort, indty, sf,
             (List.rev reified_ctors), projs, Q.quote_relevance oib.mind_relevance) :: ls, acc)
        ([],acc) (Array.to_list mib.mind_packets)
      in
      let nparams = Q.quote_int mib.Declarations.mind_nparams in
      let paramsctx, acc = quote_rel_context quote_term acc env sigma mib.Declarations.mind_params_ctxt in
      let uctx = quote_universes_decl mib.Declarations.mind_universes mib.Declarations.mind_template in
      let var = Option.map (CArray.map_to_list Q.quote_variance) mib.Declarations.mind_variance in
      let bodies = List.map Q.mk_one_inductive_body (List.rev ls) in
      let finite = Q.quote_mind_finiteness mib.Declarations.mind_finite in
      (* let templatePoly = Q.quote_bool mi.mind_template in *)
      let mind = Q.mk_mutual_inductive_body finite nparams paramsctx bodies uctx var in
      ref_name, Q.mk_inductive_decl mind, acc
    in ((fun acc env -> quote_term acc (false, env)),
        (fun acc env t mib ->
        quote_minductive_type acc (false, env) t mib))

  let quote_term env sigma trm =
    let (fn,_) = quote_term_remember (fun _ () -> ()) (fun _ _ () -> ()) in
    fst (fn () env sigma trm)

  let quote_mind_decl env sigma trm mib =
    let (_,fn) = quote_term_remember (fun _ () -> ()) (fun _ _ () -> ()) in
    let (_, indd, _) = fn () env sigma trm mib in indd

  type defType =
    Ind of Names.inductive * mutual_inductive_body
  | Const of KerName.t

  let universes_of_ctx ctx =
    Context.Rel.fold_inside (fun univs d -> Univ.Level.Set.union univs
      (Context.Rel.Declaration.fold_constr (fun c univs -> Univ.Level.Set.union univs (Vars.universes_of_constr c)) d univs))
      ~init:Univ.Level.Set.empty ctx

  let universes_of_mib mib =
    let pars = mib.mind_params_ctxt in
    let univs = universes_of_ctx pars in
      Array.fold_left (fun univs oib ->
        let univsty = universes_of_ctx oib.mind_arity_ctxt in
        Array.fold_left (fun univs cty ->
          let univscty = Vars.universes_of_constr cty in
          Univ.Level.Set.union univs univscty)
          univsty oib.mind_user_lc)
        univs mib.mind_packets

  let quote_term_rec ~bypass ?(with_universes=true) ?(with_restriction=true) env sigma trm =
    let visited_terms = ref Names.KNset.empty in
    let visited_types = ref Mindset.empty in
    let universes = ref Univ.Level.Set.empty in
    let constants = ref [] in
    let add quote_term quote_type trm acc =
      match trm with
      | Ind ((mi,idx), mib) ->
        let t = mi in
        if Mindset.mem t !visited_types then ()
        else
          begin
            visited_types := Mindset.add t !visited_types;
            let univs = universes_of_mib mib in
            let () = universes := Univ.Level.Set.union univs !universes in
            let (kn,d,acc) =
              try quote_type acc env sigma mi mib
              with e ->
                Feedback.msg_debug (str"Exception raised while checking " ++ MutInd.print mi);
                raise e
            in
            constants := (kn,d) :: !constants
          end
      | Const kn ->
        if Names.KNset.mem kn !visited_terms then ()
        else
          begin
            visited_terms := Names.KNset.add kn !visited_terms ;
            let c = Names.Constant.make kn kn in
            let cd = Environ.lookup_constant c env in
            let body = match cd.const_body with
              | Undef _ -> None
              | Primitive t ->
                  warn_primitive_turned_into_axiom (CPrimitives.to_string t);
                  None
              | Symbol _ ->
                  warn_symbol_turned_into_axiom (Constant.debug_to_string c);
                  None
              | Def cs -> Some cs
              | OpaqueDef lc ->
                if bypass then
                  let c, univs = Global.force_proof Library.indirect_accessor lc in
                  match univs with
                  | Opaqueproof.PrivateMonomorphic () -> Some c
                  | Opaqueproof.PrivatePolymorphic csts ->
                    let () =
                      if not (Univ.ContextSet.is_empty csts) then
                        warn_ignoring_private_polymorphic_universes ()
                    in Some c
                else None
            in
            let tm, acc =
              match body with
              | None -> None, acc
              | Some tm ->
                let univs = Vars.universes_of_constr tm in
                let () = universes := Univ.Level.Set.union univs !universes in
                try let (tm, acc) = quote_term acc (Global.env ()) (Evd.from_env @@ Global.env ()) tm in
                  (Some tm, acc)
                with e ->
                  Feedback.msg_debug (str"Exception raised while checking body of " ++ KerName.print kn);
                  raise e
            in
            let uctx = quote_universes_decl cd.const_universes None in
            let ty, acc =
              let ty = cd.const_type in
              let univs = Vars.universes_of_constr ty in
              let () = universes := Univ.Level.Set.union univs !universes in
              (try quote_term acc (Global.env ()) (Evd.from_env @@ Global.env ()) ty
                with e ->
                  Feedback.msg_debug (str"Exception raised while checking type of " ++ KerName.print kn);
                  raise e)
            in
            let rel = Q.quote_relevance cd.const_relevance in
            let cst_bdy = Q.mk_constant_body ty tm uctx rel in
            let decl = Q.mk_constant_decl cst_bdy in
            constants := (Q.quote_kn kn, decl) :: !constants
          end
    in
    let (quote_rem,quote_typ) =
      let a = ref (fun _ _ _ -> assert false) in
      let b = ref (fun _ _ _ -> assert false) in
      let (x,y) =
	      quote_term_remember (fun x () -> add !a !b (Const x) ())
          (fun y mib () -> add !a !b (Ind (y, mib)) ())
      in
      a := x ;
      b := y ;
      (x,y)
    in
    let (tm, _) = quote_rem () env sigma trm in
    let decls = List.fold_right (fun (kn, d) acc -> Q.add_global_decl kn d acc) !constants (Q.empty_global_declarations ()) in
    let univs =
      if with_universes then
        if with_restriction then
          let univs = Univ.Level.Set.union (Vars.universes_of_constr trm) !universes in
          let univs = Univ.Level.Set.filter (fun l -> Option.is_empty (Univ.Level.var_index l)) univs in
          quote_ugraph ~kept:univs (Environ.universes env)
        else quote_ugraph (Environ.universes env)
      else
        (debug Pp.(fun () -> str"Skipping universes: ");
         time (Pp.str"Quoting empty universe context")
           (fun uctx -> Q.quote_univ_contextset uctx) Univ.ContextSet.empty)
    in
    let retro =
      let retro = Environ.retroknowledge env in
      let quote_retro = Option.map (fun c -> Q.quote_kn (Names.Constant.canonical c)) in
      let pre =
        { Q.retro_int63 = quote_retro retro.Retroknowledge.retro_int63 ;
          Q.retro_float64 = quote_retro retro.Retroknowledge.retro_float64 ;
          Q.retro_string = quote_retro retro.Retroknowledge.retro_string ;
          Q.retro_array = quote_retro retro.Retroknowledge.retro_array }
      in Q.quote_retroknowledge pre
    in
    let env = Q.mk_global_env univs decls retro in
    Q.mk_program env tm

  let quote_rel_context env sigma ctx =
    fst (quote_rel_context (fun acc env sigma t -> (quote_term (snd env) sigma t, acc)) () ((), env) sigma ctx)

  let quote_one_ind envA envC (mi:Entries.one_inductive_entry) =
    let iname = Q.quote_ident mi.mind_entry_typename  in
    let arity = quote_term envA (Evd.from_env envA) mi.mind_entry_arity in
    let consnames = List.map Q.quote_ident (mi.mind_entry_consnames) in
    let constypes = List.map (quote_term envC (Evd.from_env envC)) (mi.mind_entry_lc) in
    (iname, arity, consnames, constypes)

  let quote_mind_params env (params: Constr.rel_context) =
    let qparams = quote_rel_context env (Evd.from_env env) params in
    (Environ.push_rel_context params env, qparams)

  let mind_params_as_types ((env,t):Environ.env*Constr.t) (params:Constr.rel_context) :
        Environ.env*Constr.t =
    (env, Term.it_mkProd_or_LetIn t params)

(*
  let empty_segment = Cooking.empty_cooking_info
  let quote_mut_ind env (mi:Declarations.mutual_inductive_body) =
   let t= Discharge.process_inductive empty_segment (Names.Cmap.empty,Names.Mindmap.empty) mi in
    let mf = Q.quote_mind_finiteness t.mind_entry_finite in
    let mp = (snd (quote_mind_params env (t.mind_entry_params))) in
    (* before quoting the types of constructors, we need to enrich the environment with the inductives *)
    let one_arities =
      List.map
        (fun x -> (x.mind_entry_typename,
                   snd (mind_params_as_types (env,x.mind_entry_arity) (t.mind_entry_params))))
        t.mind_entry_inds in
    (* env for quoting constructors of inductives. First push inductices, then params *)
    let envC = List.fold_left (fun env p -> Environ.push_rel (toDecl (Context.annotR (Names.Name (fst p)), None, snd p)) env) env (one_arities) in
    let envC = Environ.push_rel_context t.mind_entry_params envC in
    (* env for quoting arities of inductives -- just push the params *)
    let envA = Environ.push_rel_context t.mind_entry_params env in
    let is = List.map (quote_one_ind envA envC) t.mind_entry_inds in
    let uctx = quote_universes_entry t.mind_entry_universes in
    let variance = Option.map (CArray.map_to_list Q.quote_variance) t.mind_entry_variance in
    Q.quote_mutual_inductive_entry (mf, mp, is, uctx, variance) *)

  let quote_constant_body_aux bypass env evm (cd : constant_body) =
    let ty = quote_term env evm cd.const_type in
    let body =
      match cd.const_body with
      | Undef _ -> None
      | Def cs -> Some (quote_term env evm cs)
      | OpaqueDef cs ->
        if bypass
        then Some (quote_term env evm (fst (Global.force_proof Library.indirect_accessor cs)))
        else None
      | Primitive _ -> failwith "Primitive types not supported by TemplateRocq"
      | Symbol _ -> failwith "Symbols are not supported by TemplateRocq"
    in
    (ty, body)

  let quote_constant_body bypass env evm cd =
    let ty, body = quote_constant_body_aux bypass env evm cd in
    Q.mk_constant_body ty body (quote_universes_decl cd.const_universes None)
      (Q.quote_relevance cd.const_relevance)

  let quote_constant_entry bypass env evm cd =
    let (ty, body) = quote_constant_body_aux bypass env evm cd in
    let uctx = match cd.const_universes with
      | Polymorphic auctx -> Polymorphic_entry (UVars.AbstractContext.repr auctx)
      | Monomorphic -> Monomorphic_entry
    in
    let univs = quote_universes_entry uctx in
    match body with
    | None -> Q.quote_constant_entry (Right (Q.quote_parameter_entry ty univs))
    | Some body -> Q.quote_constant_entry (Left (Q.quote_definition_entry (Some ty) body univs))

  (* let quote_entry_aux bypass env evm (name:string) =
    let (dp, nm) = split_name name in
    match Nametab.locate (Libnames.make_qualid dp nm) with
    | Globnames.ConstRef c ->
      let cd = Environ.lookup_constant c env in
      (*CHANGE :  template polymorphism for definitions was removed.
                  See: https://github.com/coq/coq/commit/d9530632321c0b470ece6337cda2cf54d02d61eb *)
      Q.quote_entry (Left (quote_constant_entry bypass env evm cd))
    | Globnames.IndRef ni ->
      let c = Environ.lookup_mind (fst ni) env in (* FIX: For efficienctly, we should also export (snd ni)*)
      let miq = quote_mut_ind env c in
      Q.quote_entry (Right miq)
    | Globnames.ConstructRef _ -> raise Not_found (* FIX?: return the enclusing mutual inductive *)
    | Globnames.VarRef _ -> raise Not_found


  let quote_entry_of bypass env evm t =
    try Some (quote_entry_aux bypass env evm t)
    with Not_found -> None *)
end
