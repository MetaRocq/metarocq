open Extractable
open Plugin_core
open BasicAst
open Tm_util

open Ast_quoter
open Ast_denoter

let to_reduction_strategy (s : Common0.reductionStrategy) : Plugin_core.reduction_strategy =
  match s with
   | Common0.Coq_cbv -> Plugin_core.rs_cbv
   | Common0.Coq_cbn -> Plugin_core.rs_cbn
   | Common0.Coq_hnf -> Plugin_core.rs_hnf
   | Common0.Coq_all -> Plugin_core.rs_all
   | Common0.Coq_lazy -> Plugin_core.rs_lazy
   | Common0.Coq_unfold x -> failwith "not yet implemented: to_reduction_strategy"

let to_qualid c : Libnames.qualid =
  Libnames.qualid_of_string (unquote_string c)

let of_qualid (q : Libnames.qualid) =
  quote_string (Libnames.string_of_qualid q)

(* todo(gmm): this definition adapted from quoter.ml *)
let quote_rel_decl env sigma = function
  | Context.Rel.Declaration.LocalAssum (na, t) ->
    let t' = quote_term env sigma t in
    quote_context_decl (quote_aname na) None t'
  | Context.Rel.Declaration.LocalDef (na, b, t) ->
    let b' = quote_term env sigma b in
    let t' = quote_term env sigma t in
    quote_context_decl (quote_aname na) (Some b') t'

(* todo(gmm): this definition adapted from quoter.ml *)
let quote_rel_context env sigma ctx =
  let decls, env =
    List.fold_right (fun decl (ds, env) ->
        let x = quote_rel_decl env sigma decl in
        (x :: ds, Environ.push_rel decl env))
      ctx ([],env) in
  quote_context decls

(* todo(gmm): this definition adapted from quoter.ml (the body of quote_minductive_type) *)
let of_mib (env : Environ.env) (t : Names.MutInd.t) (mib : Plugin_core.mutual_inductive_body)
  : Ast0.Env.mutual_inductive_body =
  match quote_mind_decl env (Evd.from_env env) t mib with
  | Ast0.Env.InductiveDecl mib -> mib
  | Ast0.Env.ConstantDecl _ -> assert false

(*
let of_mib (env : Environ.env) (t : Names.MutInd.t) (mib : Plugin_core.mutual_inductive_body) : Ast0.Env.mutual_inductive_body =
  let open Declarations in
  let uctx = get_abstract_inductive_universes mib.mind_universes in
  let inst = Univ.UContext.instance uctx in
  let indtys =
    (CArray.map_to_list (fun oib ->
         let ty = Inductive.type_of_inductive ((mib,oib),inst) in
         (Context.Rel.Declaration.LocalAssum (Context.annotR (Names.Name oib.mind_typename), ty))) mib.mind_packets)
  in
  let envind = Environ.push_rel_context (List.rev indtys) env in
  let ntyps = Array.length mib.mind_packets in
  let (ls,acc) =
    List.fold_left (fun (ls,acc) oib ->
    let named_ctors =
      CList.combine3
        (Array.to_list oib.mind_consnames)
        (Array.to_list oib.mind_user_lc)
        (Array.to_list oib.mind_consnrealargs)
    in
    let indty = Inductive.type_of_inductive ((mib,oib),inst) in
    let indty = quote_term env indty in
    let indices, pars =
    let ctx = oib.mind_arity_ctxt in
      CList.chop (List.length ctx - List.length mib.mind_params_ctxt) ctx
    in
    let indices = quote_rel_context (push_rel_context pars env) indices in
    let indty = quote_term env indty in
    let indsort = Q.quote_sort (inductive_sort oib) in
    let (reified_ctors,acc) =
      List.fold_left (fun (ls,acc) (nm,ty,ar) ->
          let ty = quote_term acc ty in
          ((quote_ident nm, qargctx, Array.to_list qindices, ty, quote_int ar) :: ls, acc))
        ([],acc) named_ctors
    in
    let projs, acc =
      match mib.mind_record with
      | PrimRecord [|id, labels, rel, ps|] ->
        let ctxwolet = Vars.smash_rel_context mib.mind_params_ctxt in
        let indty = Constr.mkApp (Constr.mkIndU ((t,0),inst),
                                  Context.Rel.to_extended_vect Constr.mkRel 0 ctxwolet) in
        let indbinder = Context.Rel.Declaration.LocalAssum (Context.annotR(Names.Name id),indty) in
        let envpars = Environ.push_rel_context (indbinder :: ctxwolet) env in
        let ps, acc = CArray.fold_right2 (fun cst pb (ls,acc) ->
            let ty = quote_term envpars pb in
            let kn = cst in
            let na = quote_ident (Names.Label.to_id kn) in
            ((na, ty) :: ls, acc)) labels ps ([],acc)
        in ps, acc
      | _ -> [], acc
    in
    let relevance = quote_relevance oib.mind_relevance in
    let sf = quote_sort_family oib.mind_kelim in
    (quote_ident oib.mind_typename, indty, indsort, indices, sf,
    (List.rev reified_ctors), projs, relevance) :: ls, acc)
        ([],env) (Array.to_list mib.mind_packets)
  in
  let nparams = quote_int mib.mind_nparams in
  let paramsctx = quote_rel_context env mib.mind_params_ctxt in
  let uctx = quote_universes_decl mib.mind_universes in
  let bodies = List.map mk_one_inductive_body (List.rev ls) in
  let finite = quote_mind_finiteness mib.mind_finite in
  let variance = Option.map (CArray.map_to_list quote_variance) mib.mind_variance in
  mk_mutual_inductive_body finite nparams paramsctx bodies uctx variance*)

let to_mie (x : Ast0.mutual_inductive_entry) : Plugin_core.mutual_inductive_entry =
  failwith "to_mie"

let get_constant_body b =
  let open Declarations in
  match b with
  | Def b -> Some b
  | Undef inline -> None
  | OpaqueDef pr ->
    let proof, _ = Global.force_proof Library.indirect_accessor pr in
    (* FIXME delayed univs skipped *)
    Some proof
  | Primitive _ -> failwith "Primitives not supported by TemplateRocq"
  | Symbol _ -> failwith "Symbols are not supported by TemplateRocq"

(* note(gmm): code taken from quoter.ml (quote_entry_aux) *)
let of_constant_body (env : Environ.env) (cd : Plugin_core.constant_body) : Ast0.Env.constant_body =
  let open Declarations in
  let {const_body = body; const_type = typ; const_universes = univs; const_relevance = rel} = cd in
  Ast0.Env.({cst_type = quote_term env (Evd.from_env env) typ;
         cst_body = Option.map (quote_term env (Evd.from_env env)) (get_constant_body body);
         cst_universes = quote_universes_decl univs None;
         cst_relevance = quote_relevance rel})

(* what about the overflow?
  efficiency? extract to bigint using Rocq directives and convert to int here? *)
let of_nat (t : int) : int = t

let of_cast_kind (ck: BasicAst.cast_kind) : Constr.cast_kind =
  match ck with
  | VmCast -> Constr.VMcast
  | NativeCast -> Constr.VMcast
  | Cast -> Constr.DEFAULTcast

  (* todo(gmm): determine what of these already exist. *)
let rec to_constr_ev env (evm : Evd.evar_map) (t : Ast0.term) : Evd.evar_map * Constr.t =
  denote_term env evm t

let to_constr (t : Ast0.term) : Constr.t =
  let env = Global.env () in
  let evm = Evd.from_env env in
  snd (to_constr_ev env evm t)

let tmOfConstr (t : Constr.t) : Ast0.term tm =
  Plugin_core.with_env_evm (fun env evm -> tmReturn (quote_term env evm t))

let tmOfMib (ti : Names.MutInd.t) (t : Plugin_core.mutual_inductive_body) : Ast0.Env.mutual_inductive_body tm =
  Plugin_core.with_env_evm (fun env _ -> tmReturn (of_mib env ti t))

let tmOfConstantBody (t : Plugin_core.constant_body) : Ast0.Env.constant_body tm =
  Plugin_core.with_env_evm (fun env _ -> tmReturn (of_constant_body env t))

(*
let dbg = function
    Coq_tmReturn _ -> "tmReturn"
  | Coq_tmBind _ -> "tmBind"
  | Coq_tmPrint _ -> "tmPrint"
  | Coq_tmMsg msg -> "tmMsg"
  | Coq_tmFail err -> "tmFail"
  | Coq_tmEval (r,t) -> "tmEval"
  | Coq_tmDefinition (nm, typ, trm) -> "tmDefinition"
  | Coq_tmAxiom (nm, typ) -> "tmAxiom"
  | Coq_tmLemma (nm, typ) -> "tmLemma"
  | Coq_tmFreshName nm -> "tmFreshName"
  | Coq_tmLocate id -> "tmLocate"
  | Coq_tmLocateModule id -> "tmLocateModule"
  | Coq_tmLocateModType id -> "tmLocateModType"
  | Coq_tmCurrentModPath -> "tmCurrentModPath"
  | Coq_tmQuoteInductive kn -> "tmQuoteInductive"
  | Coq_tmQuoteUniverses -> "tmQuoteUniverses"
  | Coq_tmQuoteConstant (kn, b) -> "tmQuoteConstant"
  | Coq_tmInductive i -> "tmInductive"
  | Coq_tmExistingInstance (l, k) -> "tmExistingInstance"
  | Coq_tmInferInstance t -> "tmInferInstance"
*)

let rec interp_tm (t : 'a coq_TM) : 'a tm =
(*  Feedback.msg_debug Pp.(str (dbg t)) ; *)
  match t with
  | Coq_tmReturn x -> tmReturn x
  | Coq_tmBind (c, k) -> tmBind (interp_tm c) (fun x -> interp_tm (k x))
  | Coq_tmPrint t -> Obj.magic (tmPrint (to_constr t))
  | Coq_tmMsg msg -> Obj.magic (tmMsg (unquote_string msg))
  | Coq_tmFail err -> tmFailString (unquote_string err)
  | Coq_tmEval (r,t) ->
    tmBind (tmEval (to_reduction_strategy r) (to_constr t))
           (fun x -> Obj.magic (tmOfConstr x))
  | Coq_tmDefinition_ (opaque, nm, typ, trm) ->
    let typ =
      match typ with
        None -> None
      | Some typ -> Some (to_constr typ)
    in
    tmMap (fun x -> Obj.magic (quote_kn x))
          (tmDefinition (unquote_ident nm) ~opaque typ (to_constr trm))
  | Coq_tmAxiom (nm, typ) ->
    tmMap (fun x -> Obj.magic (quote_kn x))
          (tmAxiom (unquote_ident nm) (to_constr typ))
  | Coq_tmLemma (nm, typ) ->
    tmMap (fun x -> Obj.magic (quote_kn x))
          (tmLemma (unquote_ident nm) (to_constr typ))
  | Coq_tmFreshName nm ->
    tmMap (fun x -> Obj.magic (quote_ident x))
          (tmFreshName (unquote_ident nm))
  | Coq_tmLocate id ->
    tmMap (fun x -> Obj.magic (List.map quote_global_reference x))
          (tmLocate (to_qualid id))
  | Coq_tmLocateModule id ->
    tmMap (fun mp -> Obj.magic (List.map quote_modpath mp))
          (tmLocateModule (to_qualid id))
  | Coq_tmLocateModType id ->
    tmMap (fun mp -> Obj.magic (List.map quote_modpath mp))
          (tmLocateModType (to_qualid id))
  | Coq_tmCurrentModPath ->
    tmMap (fun mp -> Obj.magic (quote_modpath mp))
          tmCurrentModPath
  | Coq_tmQuoteInductive kn ->
    tmBind (tmQuoteInductive (unquote_kn kn))
           (function
             None -> Obj.magic (tmFail Pp.(str "inductive does not exist"))
           | Some (mi, mib) -> Obj.magic (tmOfMib mi mib))
  | Coq_tmQuoteUniverses ->
    tmMap (fun x -> Obj.magic (quote_univ_contextset x)) tmQuoteUniverses
  | Coq_tmQuoteModule id ->
    tmMap (fun x -> Obj.magic (List.map quote_global_reference x)) (tmQuoteModule (to_qualid id))
  | Coq_tmQuoteModFunctor id ->
    tmMap (fun x -> Obj.magic (List.map quote_global_reference x)) (tmQuoteModFunctor (to_qualid id))
  | Coq_tmQuoteModType id ->
    tmMap (fun x -> Obj.magic (List.map quote_global_reference x)) (tmQuoteModType (to_qualid id))
  | Coq_tmQuoteConstant (kn, b) ->
    tmBind (tmQuoteConstant (unquote_kn kn) b)
           (fun x -> Obj.magic (tmOfConstantBody x))
  | Coq_tmInductive (inferu, i) ->
    tmMap (fun _ -> Obj.magic ()) (tmInductive (unquote_bool inferu) (to_mie i))
  | Coq_tmExistingInstance (locality, k) ->
    Obj.magic (tmExistingInstance (unquote_hint_locality locality) (unquote_global_reference k))
  | Coq_tmInferInstance t ->
    tmBind (tmInferInstance (to_constr t))
      (function
          None -> Obj.magic None
        | Some inst -> Obj.magic (tmMap (fun x -> Some x) (tmOfConstr inst)))

let run_vernac ~pm (c : 'a coq_TM) : Plugin_core.coq_state =
  Plugin_core.run_vernac ~st:pm (interp_tm (Obj.magic c))
