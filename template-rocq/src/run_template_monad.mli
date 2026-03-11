val declare_inductive : Environ.env -> Evd.evar_map -> bool -> Constr.t -> Evd.evar_map

val run_template_program_rec :
  Global.indirect_accessor ->
  poly:bool ->
  ?intactic:bool ->
  Constr.t Plugin_core.cont ->
  st:Plugin_core.coq_state ->
  Environ.env -> Evd.evar_map * Constr.t ->
  Plugin_core.coq_state
