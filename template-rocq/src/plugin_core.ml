(* this file is the interface that extracted plugins will use.
 *)

type ident   = Names.Id.t (* Template.BasicAst.ident *)
type qualid  = Libnames.qualid (* Template.BasicAst.qualid *)
type kername = Names.KerName.t (* Template.BasicAst.kername *)
type reduction_strategy = Redexpr.red_expr (* Template.TemplateMonad.Common.reductionStrategy *)
type global_reference = Names.GlobRef.t (* Template.Ast.global_reference *)
type term = Constr.t  (* Template.Ast.term *)
type mutual_inductive_body = Declarations.mutual_inductive_body (* Template.Ast.mutual_inductive_body *)
type constant_body = Declarations.constant_body
type constant_entry = Entries.constant_entry (* Template.Ast.constant_entry *)
type mutual_inductive_entry = Entries.mutual_inductive_entry (* Template.Ast.mutual_inductive_entry *)

let default_flags = Redops.make_red_flag Genredexpr.[FBeta;FMatch;FFix;FCofix;FZeta;FDeltaBut []]
let rs_cbv = Genredexpr.Cbv default_flags
let rs_cbn = Genredexpr.Cbn default_flags
let rs_hnf = Genredexpr.Hnf
let rs_all = Genredexpr.Cbv Redops.all_flags
let rs_lazy = Genredexpr.Cbv Redops.all_flags
let rs_unfold (env : Environ.env) (gr : global_reference) =
  try
    Genredexpr.Unfold [Locus.AllOccurrences,
                       Tacred.evaluable_of_global_reference env gr]
  with
  | _ -> CErrors.user_err
           Pp.(str "Constant not found or not a constant: " ++ Printer.pr_global gr)

(* Rocq state related to vernaculars, needed to declare constants,
   could be a good idea to add the evar_map / env here as a record *)
type coq_state = Declare.OblState.t

type 'a cont = st:coq_state -> Environ.env -> Evd.evar_map -> 'a -> coq_state
type 'a tm =
  st:coq_state -> Environ.env -> Evd.evar_map
  -> 'a cont -> (st:coq_state -> Pp.t -> coq_state) -> coq_state

let run ~st (c : 'a tm) env evm (k : st:coq_state -> Environ.env -> Evd.evar_map -> 'a -> coq_state) : coq_state =
  c ~st env evm k (fun ~st x -> CErrors.user_err x)

let run_vernac ~st (c : 'a tm) : coq_state =
  let env = Global.env () in
  let evm = Evd.from_env env in
  run ~st c env evm (fun ~st _ _ _ -> st)

let with_env_evm (c : Environ.env -> Evd.evar_map -> 'a tm) : 'a tm =
  fun ~st env evm success fail -> c ~st env evm env evm success fail

let tmReturn (x : 'a) : 'a tm =
  fun ~st env evd k _fail -> k ~st env evd x

let tmBind (x : 'a tm) (k : 'a -> 'b tm) : 'b tm =
  fun ~st env evd success fail ->
        x ~st env evd (fun ~st env evd v -> k v ~st env evd success fail) fail

let tmMap (f : 'a -> 'b) (x : 'a tm) : 'b tm =
  fun ~st env evd success fail ->
        x ~st env evd (fun ~st env evd v -> success ~st env evd (f v)) fail

let tmPrint (t : term) : unit tm =
  fun ~st env evd success _fail ->
    let _ = Feedback.msg_info (Printer.pr_constr_env env evd t) in
    success ~st env evd ()

let tmMsg (s : string) : unit tm =
  fun ~st env evd success _fail ->
    let _ = Feedback.msg_info (Pp.str s) in
    success ~st env evd ()

let tmFail (s : Pp.t) : 'a tm =
  fun ~st _ _ _ fail -> fail ~st s

let tmFailString (s : string) : 'a tm =
  tmFail Pp.(str s)


let reduce env evm red trm =
  let red, _ = Redexpr.reduction_of_red_expr env red in
  let evm, red = red env evm (EConstr.of_constr trm) in
  (evm, EConstr.to_constr evm red)

let tmEval (rd : reduction_strategy) (t : term) : term tm =
  fun ~st env evd k _fail ->
    let evd,t' = reduce env evd rd t in
    k ~st env evd t'

let tmDefinition (nm : ident) ?(poly=PolyFlags.default) ?opaque:(opaque=false) (typ : term option) (body : term) : kername tm =
  fun ~st env evm success _fail ->
    let cinfo = Declare.CInfo.make ~name:nm ~typ:(Option.map EConstr.of_constr typ) () in
    let info = Declare.Info.make ~poly ~kind:(Decls.(IsDefinition Definition)) () in
    let n = Declare.declare_definition ~cinfo ~info ~opaque ~body:(EConstr.of_constr body) evm in
    let env = Global.env () in
    let evm = Evd.from_env env in
    success ~st env evm (Names.Constant.canonical (Globnames.destConstRef n))

let tmAxiom (nm : ident) ?(poly=PolyFlags.default) (typ : term) : kername tm =
  fun ~st env evm success _fail ->
    let univs = Evd.univ_entry ~poly evm in
    let param =
      let entry = Declare.parameter_entry ~univs typ in
      Declare.ParameterEntry entry
    in
    let n =
      Declare.declare_constant ~name:nm
        ~kind:(Decls.IsDefinition Decls.Definition)
        param
    in
    success ~st (Global.env ()) evm (Names.Constant.canonical n)

(* this generates a lemma leaving a hole *)
let tmLemma (nm : ident) ?(poly=PolyFlags.default) (ty : term) : kername tm =
  fun ~st env evm success _fail ->
    let kind = Decls.(IsDefinition Definition) in
    let hole = CAst.make (Constrexpr.CHole (Some Evar_kinds.(GQuestionMark default_question_mark))) in
    Feedback.msg_debug (Pp.str "interp_casted called");
    let evm, (c, _) =
      try Constrintern.interp_casted_constr_evars_impls ~program_mode:true env evm hole (EConstr.of_constr ty)
      with e -> Feedback.msg_debug (Pp.str "interp_casted raised"); raise e in
    RetrieveObl.check_evars env evm;
    let obls, _, c, cty = RetrieveObl.retrieve_obligations env nm evm 0 c (EConstr.of_constr ty) in
    (* let evm = Evd.minimize_universes evm in *)
    let ctx = Evd.ustate evm in
    let obl_hook = Declare.Hook.make_g (fun { Declare.Hook.S.dref = gr } pm ->
        let env = Global.env () in
        let evm = Evd.from_env env in
        let evm, t = Evd.fresh_global env evm gr in
        match Constr.kind (EConstr.to_constr evm t) with
        | Constr.Const (tm, _) ->
          success ~st:pm env evm (Names.Constant.canonical tm)
        | _ -> failwith "Evd.fresh_global did not return a Const") in
    let cinfo = Declare.CInfo.make ~name:nm ~typ:cty () in
    let info = Declare.Info.make ~poly ~kind () in
    (* This should register properly with the interpretation extension *)
    Declare.Obls.add_definition ~pm:st ~cinfo ~info ~body:c ~uctx:ctx ~obl_hook ~opaque:false obls

let tmFreshName (nm : ident) : ident tm =
  fun ~st env evd success _fail ->
    let name' =
      Namegen.next_ident_away_from nm (fun id -> Nametab.exists_cci (Lib.make_path id))
    in success ~st env evd name'

let tmLocate (qualid : qualid) : global_reference list tm =
  fun ~st env evd success _fail ->
  let grs = Nametab.locate_all qualid in success ~st env evd grs

let tmLocateModule (qualid : qualid) : Names.ModPath.t list tm =
  fun ~st env evd success _fail ->
  let mps = Nametab.locate_extended_all_module qualid in success ~st env evd mps

let tmLocateModType (qualid : qualid) : Names.ModPath.t list tm =
  fun ~st env evd success _fail ->
  let mps = Nametab.locate_extended_all_modtype qualid in success ~st env evd mps

let tmLocateString (s : string) : global_reference list tm =
  let id = Libnames.qualid_of_string s in
  tmLocate id

let tmLocateModuleString (s : string) : Names.ModPath.t list tm =
  let id = Libnames.qualid_of_string s in
  tmLocateModule id

let tmLocateModTypeString (s : string) : Names.ModPath.t list tm =
  let id = Libnames.qualid_of_string s in
  tmLocateModType id

let tmCurrentModPath : Names.ModPath.t tm =
  fun ~st env evd success _fail ->
    let mp = Lib.current_mp () in success ~st env evd mp

let tmQuoteInductive (kn : kername) : (Names.MutInd.t * mutual_inductive_body) option tm =
  fun ~st env evm success _fail ->
    try
      let mi = Names.MutInd.make1 kn in
      let mind = Environ.lookup_mind mi env in
      success ~st env evm (Some (mi, mind))
    with
      Not_found -> success ~st env evm None

let tmQuoteUniverses : UGraph.t tm =
  fun ~st env evm success _fail ->
    success ~st env evm (Environ.universes env)

let quote_module ~(include_functor : bool) ~(include_submodule : bool) ~(include_submodtype : bool) (qualid : qualid) : global_reference list =
  let mp = Nametab.locate_module qualid in
  let mb = Global.lookup_module mp in
  let open Declarations in
  let open Mod_declarations in
  let rec aux mb mp =
    let rec aux' mt mp =
      match mt with
      | MoreFunctor (_, _, body) -> if include_functor then aux' body mp else []
      | NoFunctor body ->
        let get_ref (label, field) =
          let open Names in
          match field with
          | SFBconst _ -> [GlobRef.ConstRef (Constant.make2 mp label)]
          | SFBmind _ -> [GlobRef.IndRef (MutInd.make2 mp label, 0)]
          | SFBrules _ -> failwith "Rewrite rules are not supported by TemplateRocq"
          | SFBmodule mb -> if include_submodule then aux (mod_type mb) (ModPath.MPdot (mp, label)) else []
          | SFBmodtype mtb -> if include_submodtype then aux (mod_type mtb) (ModPath.MPdot (mp, label)) else []
        in
        CList.map_append get_ref body
    in aux' mb mp
  in aux (mod_type mb) mp

let tmQuoteModule (qualid : qualid) : global_reference list tm =
  fun ~st env evd success _fail ->
  let include_functor = false in
  let include_submodule = true in
  let include_submodtype = false in
  success ~st env evd (quote_module ~include_functor ~include_submodule ~include_submodtype qualid)

let tmQuoteModFunctor (qualid : qualid) : global_reference list tm =
  fun ~st env evd success _fail ->
  let include_functor = true in
  let include_submodule = true in
  let include_submodtype = false in
  success ~st env evd (quote_module ~include_functor ~include_submodule ~include_submodtype qualid)

let tmQuoteModType (qualid : qualid) : global_reference list tm =
  fun ~st env evd success _fail ->
  let include_functor = true in
  let include_submodule = true in
  let include_submodtype = true in
  success ~st env evd (quote_module ~include_functor ~include_submodule ~include_submodtype qualid)

(*let universes_entry_of_decl ?withctx d =
  let open Declarations in
  let open Entries in
  match d with
  | Monomorphic ctx ->
    (match withctx with
    | Some ctx' -> Monomorphic_entry (Univ.ContextSet.union ctx ctx')
    | None -> Monomorphic_entry ctx)
  | Polymorphic ctx ->
    assert(Option.is_empty withctx);
    Polymorphic_entry (Univ.AUContext.names ctx, Univ.AUContext.repr ctx)*)
(*
let _constant_entry_of_cb (cb : Declarations.constant_body) =
  let open Declarations in
  let open Entries in
  let secctx = match cb.const_hyps with [] -> None | l -> Some l in
  let with_body_opaque b ?withctx opaque =
    Entries.{ const_entry_secctx = secctx;
    const_entry_feedback = None;
    const_entry_type = Some cb.const_type;
    const_entry_body = Future.from_val ((b, Univ.ContextSet.empty), Safe_typing.empty_private_constants);
    const_entry_universes = universes_entry_of_decl ?withctx cb.const_universes;
    const_entry_opaque = opaque;
    const_entry_inline_code = cb.const_inline_code }
  in
  let parameter inline = { parameter_entry_secctx = secctx;
    parameter_entry_type = cb.const_type;
    parameter_entry_universes = universes_entry_of_decl cb.const_universes;
    parameter_entry_inline_code = inline }
  in
  match cb.const_body with
  | Def b -> DefinitionEntry (with_body_opaque (Mod_subst.force_constr b) false)
  | Undef inline -> ParameterEntry (parameter inline)
  | OpaqueDef pr ->
    let opaquetab = Global.opaque_tables () in
    let proof = Opaqueproof.force_proof opaquetab pr in
    let ctx = Opaqueproof.force_constraints opaquetab pr in
    DefinitionEntry (with_body_opaque proof ~withctx:ctx true)
  | Primitive _ -> failwith "Primitives not supported by TemplateRocq"

*)

(* get the definition associated to a kername *)
let tmQuoteConstant (kn : kername) (bypass : bool) : Declarations.constant_body tm =
  fun ~st env evd success fail ->
    (* todo(gmm): there is a bug here *)
    try
      let cnst = Environ.lookup_constant (Names.Constant.make1 kn) env in
      success ~st env evd cnst
    with
      Not_found -> fail ~st Pp.(str "constant not found " ++ Names.KerName.print kn)

let tmInductive (infer_univs : bool) (mie : mutual_inductive_entry) : unit tm =
  fun ~st env evd success _fail ->
    let mie =
      if infer_univs then
        let evm = Evd.from_env env in
        let ctx, mie = Tm_util.RetypeMindEntry.infer_mentry_univs env evm mie in
        let () = Global.push_context_set ctx in
        mie
      else mie
    in
    let names = (UState.Monomorphic_entry Univ.ContextSet.empty, UnivNames.empty_binders) in
    ignore (DeclareInd.declare_mutual_inductive_with_eliminations mie names []) ;
    success ~st (Global.env ()) evd ()

let tmExistingInstance (locality : Hints.hint_locality) (gr : Names.GlobRef.t) : unit tm =
  fun ~st env evd success _fail ->
    Classes.existing_instance locality gr None;
    success ~st env evd ()

let tmInferInstance (typ : term) : term option tm =
  fun ~st env evm success fail ->
    try
      let (evm,t) = Class_tactics.resolve_one_typeclass env evm (EConstr.of_constr typ) in
      success ~st env evm (Some (EConstr.to_constr evm t))
    with
      Not_found -> success ~st env evm None
