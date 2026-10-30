open Names
open GlobRef
open Pp

let resolve (tm : string) : GlobRef.t Lazy.t =
  lazy (Rocqlib.lib_ref tm)

let r_template_monad_prop_p s = resolve ("metarocq.templatemonad.prop." ^ s)
let r_template_monad_type_p s = resolve ("metarocq.templatemonad.type." ^ s)

(* for "Core" *)
let (ptmReturn,
     ptmBind,

     ptmPrint,
     ptmMsg,
     ptmFail,

     ptmEval,

     ptmLemma,
     ptmDefinitionRed,
     ptmAxiomRed,
     ptmMkDefinition,
     ptmMkInductive,
     ptmVariable,

     ptmFreshName,

     ptmLocate,
     ptmLocateModule,
     ptmLocateModType,
     ptmCurrentModPath,

     ptmQuote,
     ptmQuoteRecTransp,
     ptmQuoteInductive,
     ptmQuoteConstant,
     ptmQuoteUniverses,
     ptmQuoteModule,
     ptmQuoteModFunctor,
     ptmQuoteModType,

     ptmUnquote,
     ptmUnquoteTyped,

     ptmInferInstance,
     ptmExistingInstance,

     ptmTestQuote,
     ptmTestUnquote,
     ptmQuoteDefinition,
     ptmQuoteDefinitionRed,
     ptmQuoteRecDefinition) =
  (r_template_monad_prop_p "tmReturn",
   r_template_monad_prop_p "tmBind",

   r_template_monad_prop_p "tmPrint",
   r_template_monad_prop_p "tmMsg",
   r_template_monad_prop_p "tmFail",

   r_template_monad_prop_p "tmEval",

   r_template_monad_prop_p "tmLemma",
   r_template_monad_prop_p "tmDefinitionRed_",
   r_template_monad_prop_p "tmAxiomRed",
   r_template_monad_prop_p "tmMkDefinition",
   r_template_monad_prop_p "tmMkInductive",
   r_template_monad_prop_p "tmVariable",

   r_template_monad_prop_p "tmFreshName",

   r_template_monad_prop_p "tmLocate",
   r_template_monad_prop_p "tmLocateModule",
   r_template_monad_prop_p "tmLocateModType",
   r_template_monad_prop_p "tmCurrentModPath",

   r_template_monad_prop_p "tmQuote",
   r_template_monad_prop_p "tmQuoteRecTransp",
   r_template_monad_prop_p "tmQuoteInductive",
   r_template_monad_prop_p "tmQuoteConstant",
   r_template_monad_prop_p "tmQuoteUniverses",
   r_template_monad_prop_p "tmQuoteModule",
   r_template_monad_prop_p "tmQuoteModFunctor",
   r_template_monad_prop_p "tmQuoteModType",

   r_template_monad_prop_p "tmUnquote",
   r_template_monad_prop_p "tmUnquoteTyped",

   r_template_monad_prop_p "tmInferInstance",
   r_template_monad_prop_p "tmExistingInstance",

   r_template_monad_prop_p "tmTestQuote",
   r_template_monad_prop_p "tmTestUnquote",
   r_template_monad_prop_p "tmQuoteDefinition",
   r_template_monad_prop_p "tmQuoteDefinitionRed",
   r_template_monad_prop_p "tmQuoteRecDefinition")

(* for "Extractable" *)
let (ttmReturn,
     ttmBind,
     ttmPrintTerm,
     ttmMsg,
     ttmFail,
     ttmEval,

     ttmDefinition,
     ttmAxiom,
     ttmLemma,
     ttmFreshName,
     ttmLocate,
     ttmLocateModule,
     ttmLocateModType,
     ttmCurrentModPath,
     ttmQuoteInductive,
     ttmQuoteUniverses,
     ttmQuoteModule,
     ttmQuoteModFunctor,
     ttmQuoteModType,
     ttmQuoteConstant,
     ttmInductive,
     ttmInferInstance,
     ttmExistingInstance) =
  (r_template_monad_type_p "tmReturn",
   r_template_monad_type_p "tmBind",

   r_template_monad_type_p "tmPrint",
   r_template_monad_type_p "tmMsg",
   r_template_monad_type_p "tmFail",
   r_template_monad_type_p "tmEval",

   r_template_monad_type_p "tmDefinition_",
   r_template_monad_type_p "tmAxiom",
   r_template_monad_type_p "tmLemma",

   r_template_monad_type_p "tmFreshName",

   r_template_monad_type_p "tmLocate",
   r_template_monad_type_p "tmLocateModule",
   r_template_monad_type_p "tmLocateModType",
   r_template_monad_type_p "tmCurrentModPath",

   r_template_monad_type_p "tmQuoteInductive",
   r_template_monad_type_p "tmQuoteUniverses",
   r_template_monad_type_p "tmQuoteModule",
   r_template_monad_type_p "tmQuoteModFunctor",
   r_template_monad_type_p "tmQuoteModType",
   r_template_monad_type_p "tmQuoteConstant",

   r_template_monad_type_p "tmInductive",

   r_template_monad_type_p "tmInferInstance",
   r_template_monad_type_p "tmExistingInstance")

type constr = Constr.t

open Tm_util.Debug

type template_monad =
    TmReturn of Constr.t
  | TmBind  of Constr.t * Constr.t

    (* printing *)
  | TmPrint of Constr.t      (* only Prop *)
  | TmPrintTerm of Constr.t  (* only Extractable *)
  | TmMsg of Constr.t
  | TmFail of Constr.t

    (* evaluation *)
  | TmEval of Constr.t * Constr.t      (* only Prop *)
  | TmEvalTerm of Constr.t * Constr.t  (* only Extractable *)

    (* creating definitions *)
  | TmDefinition of Constr.t * Constr.t * Constr.t * Constr.t * Constr.t
  | TmDefinitionTerm of Constr.t * Constr.t * Constr.t * Constr.t
  | TmLemma of Constr.t * Constr.t
  | TmLemmaTerm of Constr.t * Constr.t
  | TmAxiom of Constr.t * Constr.t * Constr.t
  | TmAxiomTerm of Constr.t * Constr.t
  | TmMkInductive of Constr.t * Constr.t
  | TmVariable of Constr.t * Constr.t

  | TmFreshName of Constr.t

  | TmLocate of Constr.t
  | TmLocateModule of Constr.t
  | TmLocateModType of Constr.t
  | TmCurrentModPath

    (* quoting *)
  | TmQuote of Constr.t (* only Prop *)
  | TmQuoteRecTransp of Constr.t * Constr.t (* arguments: recursive * bypass opacity * term  *)  (* only Prop *)
  | TmQuoteInd of Constr.t * bool (* strict *)
  | TmQuoteConst of Constr.t * Constr.t * bool (* strict *)
  | TmQuoteUnivs
  | TmQuoteModule of Constr.t
  | TmQuoteModFunctor of Constr.t
  | TmQuoteModType of Constr.t

  | TmUnquote of Constr.t                   (* only Prop *)
  | TmUnquoteTyped of Constr.t * Constr.t (* only Prop *)

    (* typeclass resolution *)
  | TmExistingInstance of Constr.t * Constr.t
  | TmInferInstance of Constr.t * Constr.t (* only Prop *)
  | TmInferInstanceTerm of Constr.t        (* only Extractable *)

(* todo: the recursive call is uneeded provided we call it on well formed terms *)
let rec app_full trm acc =
  match Constr.kind trm with
    Constr.App (f, xs) -> app_full f (Array.to_list xs @ acc)
  | _ -> (trm, acc)

let monad_failure s k =
  CErrors.user_err  Pp.(str s ++ str " must take " ++ int k ++
                          str " argument" ++ str (if k > 0 then "s" else "") ++ str "." ++ fnl () ++
                          str "Please file a bug with MetaRocq.")

let next_action env evd (pgm : constr) : template_monad * _ =
  let () = ppdebug 2 (fun () -> Pp.(str "MetaRocq: TemplateProgram: Going to reduce " ++ fnl () ++ Printer.pr_constr_env env evd pgm)) in
  let pgm = Reduction.whd_all env pgm in
  let (coConstr, args) = app_full pgm [] in
  let (glob_ref, universes) =
    try
      let open Constr in
      match kind coConstr with
      | Const (c, u) -> ConstRef c, u
      | Ind (i, u) -> IndRef i, u
      | Construct (c, u) -> ConstructRef c, u
      | Var id -> VarRef id, UVars.Instance.empty
      | _ -> raise Not_found
    with _ ->
      CErrors.user_err (str "Invalid argument or not yet implemented. The argument must be a TemplateProgram: " ++ Printer.pr_constr_env env evd coConstr)
  in
  let eq_gr t = Environ.QGlobRef.equal env glob_ref (Lazy.force t) in
  if eq_gr ptmBind || eq_gr ttmBind then
    let () = ppdebug 1 (fun () -> Pp.(str "MetaRocq: TemplateProgram: processing tmBind")) in
    match args with
    | _::_::a::f::[] ->
       (TmBind (a, f), universes)
    | _ -> monad_failure "tmBind" 4
  else
    let () = ppdebug 0 (fun () -> Pp.(str "MetaRocq: TemplateProgram: Going to run:" ++ fnl () ++ Printer.pr_constr_env env evd pgm)) in
    if eq_gr ptmReturn || eq_gr ttmReturn then
      match args with
      | _::h::[] ->
        (TmReturn h, universes)
      | _ -> monad_failure "tmReturn" 2
  else if eq_gr ptmPrint then
    match args with
    | _::trm::[] ->
       (TmPrint trm, universes)
    | _ -> monad_failure "tmPrint" 2
  else if eq_gr ttmPrintTerm then
    match args with
    | trm::[] ->
       (TmPrintTerm trm, universes)
    | _ -> monad_failure "tmPrint" 1
  else if eq_gr ptmMsg || eq_gr ttmMsg then
    match args with
    | trm::[] ->
       (TmMsg trm, universes)
    | _ -> monad_failure "tmMsg" 2
  else if eq_gr ptmFail || eq_gr ttmFail then
    match args with
    | _::trm::[] ->
       (TmFail trm, universes)
    | _ -> monad_failure "tmFail" 2
  else if eq_gr ptmEval then
    match args with
    | strat::_::trm::[] -> (TmEval (strat, trm), universes)
    | _ -> monad_failure "tmEval" 3
  else if eq_gr ttmEval then
    match args with
    | strat::trm::[] -> (TmEvalTerm (strat, trm), universes)
    | _ -> monad_failure "tmEval" 2

  else if eq_gr ptmDefinitionRed then
    match args with
    | opaque::name::s::typ::body::[] ->
      (TmDefinition (opaque, name, s, typ, body), universes)
    | _ -> monad_failure "tmDefinitionRed" 4
  else if eq_gr ttmDefinition then
    match args with
    | opaque::name::typ::body::[] ->
       (TmDefinitionTerm (opaque, name, typ, body), universes)
    | _ -> monad_failure "tmDefinition" 4

  else if eq_gr ptmLemma then
    match args with
    | name::typ::[] ->
       (TmLemma (name,typ), universes)
    | _ -> monad_failure "tmLemma" 2
  else if eq_gr ttmLemma then
    match args with
    | name::typ::[] ->
       (TmLemmaTerm (name, typ), universes)
    | _ -> monad_failure "tmLemma" 2

  else if eq_gr ptmAxiomRed then
    match args with
    | name::s::typ::[] ->
      (TmAxiom (name,s,typ), universes)
    | _ -> monad_failure "tmAxiomRed" 3
  else if eq_gr ttmAxiom then
    match args with
    | name::typ::[] ->
       (TmAxiomTerm (name, typ), universes)
    | _ -> monad_failure "tmAxiom" 2

  else if eq_gr ptmFreshName || eq_gr ttmFreshName then
    match args with
    | name::[] ->
       (TmFreshName name, universes)
    | _ -> monad_failure "tmFreshName" 1

  else if eq_gr ptmLocate || eq_gr ttmLocate then
    match args with
    | id::[] ->
       (TmLocate id, universes)
    | _ -> monad_failure "tmLocate" 1
  else if eq_gr ptmLocateModule || eq_gr ttmLocateModule then
    match args with
    | id::[] ->
       (TmLocateModule id, universes)
    | _ -> monad_failure "tmLocateModule" 1
  else if eq_gr ptmLocateModType || eq_gr ttmLocateModType then
    match args with
    | id::[] ->
       (TmLocateModType id, universes)
    | _ -> monad_failure "tmLocateModType" 1
  else if eq_gr ptmCurrentModPath then
    match args with
    | _::[] -> (TmCurrentModPath, universes)
    | _ -> monad_failure "tmCurrentModPath" 1
  else if eq_gr ttmCurrentModPath then
    match args with
    | [] -> (TmCurrentModPath, universes)
    | _ -> monad_failure "tmCurrentModPath" 1

  else if eq_gr ptmQuote then
    match args with
    | _::trm::[] ->
       (TmQuote trm, universes)
    | _ -> monad_failure "tmQuote" 3
  else if eq_gr ptmQuoteRecTransp then
    match args with
    | _::trm::bypass::[] ->
       (TmQuoteRecTransp (bypass,trm), universes)
    | _ -> monad_failure "tmQuoteRec" 3


  else if eq_gr ptmQuoteInductive then
    match args with
    | name::[] ->
       (TmQuoteInd (name, false), universes)
    | _ -> monad_failure "tmQuoteInductive" 1
  else if eq_gr ttmQuoteInductive then
    match args with
    | name::[] ->
       (TmQuoteInd (name, true), universes)
    | _ -> monad_failure "tmQuoteInductive" 1

  else if eq_gr ptmQuoteUniverses || eq_gr ttmQuoteUniverses then
    match args with
    | [] ->
       (TmQuoteUnivs, universes)
    | _ -> monad_failure "tmQuoteUniverses" 0
  else if eq_gr ptmQuoteModule || eq_gr ttmQuoteModule then
    match args with
    | [id] ->
       (TmQuoteModule id, universes)
    | _ -> monad_failure "tmQuoteModule" 0
  else if eq_gr ptmQuoteModFunctor || eq_gr ttmQuoteModFunctor then
    match args with
    | [id] ->
       (TmQuoteModFunctor id, universes)
    | _ -> monad_failure "tmQuoteModFunctor" 0
  else if eq_gr ptmQuoteModType || eq_gr ttmQuoteModType then
    match args with
    | [id] ->
       (TmQuoteModType id, universes)
    | _ -> monad_failure "tmQuoteModType" 0
  else if eq_gr ptmQuoteConstant then
    match args with
    | name::bypass::[] ->
       (TmQuoteConst (name, bypass, false), universes)
    | _ -> monad_failure "tmQuoteConstant" 2
  else if eq_gr ttmQuoteConstant then
    match args with
    | name::bypass::[] ->
       (TmQuoteConst (name, bypass, true), universes)
    | _ -> monad_failure "tmQuoteConstant" 2

  else if eq_gr ptmMkInductive then
    match args with
    | inferu :: mind :: [] -> (TmMkInductive (inferu, mind), universes)
    | _ -> monad_failure "tmMkInductive" 1
  else if eq_gr ptmVariable then
    match args with
    | name::ty::[] -> (TmVariable (name,ty) , universes)
    | _ -> monad_failure "tmVariable" 2
  else if eq_gr ttmInductive then
    match args with
    | inferu :: mind::[] -> (TmMkInductive (inferu, mind), universes)
    | _ -> monad_failure "tmInductive" 1
  else if eq_gr ptmUnquote then
    match args with
    | t::[] ->
       (TmUnquote t, universes)
    | _ -> monad_failure "tmUnquote" 1
  else if eq_gr ptmUnquoteTyped then
    match args with
    | typ::t::[] ->
       (TmUnquoteTyped (typ, t), universes)
    | _ -> monad_failure "tmUnquoteTyped" 2

  else if eq_gr ptmExistingInstance || eq_gr ttmExistingInstance then
    match args with
    | locality :: name :: [] ->
       (TmExistingInstance (locality, name), universes)
    | _ -> monad_failure "tmExistingInstance" 2
  else if eq_gr ptmInferInstance then
    match args with
    | s :: typ :: [] ->
       (TmInferInstance (s, typ), universes)
    | _ -> monad_failure "tmInferInstance" 2
  else if eq_gr ttmInferInstance then
    match args with
    | typ :: [] ->
       (TmInferInstanceTerm typ, universes)
    | _ -> monad_failure "tmInferInstance" 2

  else CErrors.user_err (str "Invalid argument or not yet implemented. The argument must be a TemplateProgram: " ++ Printer.pr_constr_env env evd coConstr)
