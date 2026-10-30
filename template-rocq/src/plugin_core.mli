(* this file is the interface that extracted plugins will use.
 *)

type ident   = Names.Id.t (* Template.BasicAst.ident *)
type qualid  = Libnames.qualid (* Template.BasicAst.ident *)
type kername = Names.KerName.t (* Template.BasicAst.kername *)
type reduction_strategy = Redexpr.red_expr (* Template.TemplateMonad.Common.reductionStrategy *)
type global_reference = Names.GlobRef.t (* Template.Ast.global_reference *)
type term = Constr.t  (* Template.Ast.term *)
type mutual_inductive_body = Declarations.mutual_inductive_body (* Template.Ast.mutual_inductive_body *)
type constant_body = Declarations.constant_body
type constant_entry = Entries.constant_entry (* Template.Ast.constant_entry *)
type mutual_inductive_entry = Entries.mutual_inductive_entry (* Template.Ast.mutual_inductive_entry *)

val rs_cbv : reduction_strategy
val rs_cbn : reduction_strategy
val rs_hnf : reduction_strategy
val rs_all : reduction_strategy
val rs_lazy : reduction_strategy
val rs_unfold : Environ.env -> global_reference -> reduction_strategy

type 'a tm

type coq_state = Declare.OblState.t
type 'a cont = st:coq_state -> Environ.env -> Evd.evar_map -> 'a -> coq_state

val run : st:coq_state
  -> 'a tm
  -> Environ.env
  -> Evd.evar_map
  -> 'a cont
  -> coq_state

val with_env_evm : (Environ.env -> Evd.evar_map -> 'a tm) -> 'a tm

val run_vernac : st:coq_state -> 'a tm -> coq_state

val tmReturn : 'a -> 'a tm
val tmBind : 'a tm -> ('a -> 'b tm) -> 'b tm
val tmMap  : ('a -> 'b) -> 'a tm -> 'b tm

val tmPrint : term -> unit tm
val tmMsg  : string -> unit tm

val tmFail : Pp.t -> 'a tm
val tmFailString : string -> 'a tm
val reduce : Environ.env -> Evd.evar_map -> reduction_strategy -> term -> Evd.evar_map * term
val tmEval : reduction_strategy -> term -> term tm

val tmDefinition : ident -> ?poly:PolyFlags.t -> ?opaque:bool -> term option -> term -> kername tm
val tmAxiom : ident -> ?poly:PolyFlags.t -> term -> kername tm
val tmLemma : ident -> ?poly:PolyFlags.t -> term -> kername tm

val tmFreshName : ident -> ident tm

val tmLocate : qualid -> global_reference list tm
val tmLocateModule : qualid -> Names.ModPath.t list tm
val tmLocateModType : qualid -> Names.ModPath.t list tm
val tmLocateString : string -> global_reference list tm
val tmLocateModuleString : string -> Names.ModPath.t list tm
val tmLocateModTypeString : string -> Names.ModPath.t list tm
val tmCurrentModPath : Names.ModPath.t tm

val tmQuoteInductive : kername -> (Names.MutInd.t * mutual_inductive_body) option tm
val tmQuoteUniverses : UGraph.t tm
val tmQuoteConstant : kername -> bool -> constant_body tm
val tmQuoteModule : qualid -> global_reference list tm
val tmQuoteModFunctor : qualid -> global_reference list tm
val tmQuoteModType : qualid -> global_reference list tm

val tmInductive : bool -> mutual_inductive_entry -> unit tm

val tmExistingInstance : Hints.hint_locality -> global_reference -> unit tm
val tmInferInstance : term -> term option tm
