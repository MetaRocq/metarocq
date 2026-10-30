val ptmTestQuote : Names.GlobRef.t Lazy.t
val ptmTestUnquote : Names.GlobRef.t Lazy.t
val ptmQuoteDefinition : Names.GlobRef.t Lazy.t
val ptmQuoteDefinitionRed : Names.GlobRef.t Lazy.t
val ptmQuoteRecDefinition : Names.GlobRef.t Lazy.t
val ptmMkDefinition : Names.GlobRef.t Lazy.t
val ptmMkInductive : Names.GlobRef.t Lazy.t


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
  | TmQuote of Constr.t (* arguments: recursive * bypass opacity * term  *)  (* only Prop *)
  | TmQuoteRecTransp of Constr.t * Constr.t
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


val app_full
  : Constr.constr -> Constr.constr list -> Constr.constr * Constr.constr list


val next_action
  : Environ.env -> Evd.evar_map -> Constr.t -> (template_monad * UVars.Instance.t)
