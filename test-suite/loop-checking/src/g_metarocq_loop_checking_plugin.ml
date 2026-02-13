
# 1 "src/g_metarocq_loop_checking_plugin.mlg"
 
open Stdarg
open LoopCheckingPlugin


let _ = Mltop.add_known_module "rocq-metarocq-loop-checking.plugin"
let () = Vernacextend.static_vernac_extend ~plugin:(Some "rocq-metarocq-loop-checking.plugin") ~command:"Check_universes" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML
         (false,
          Vernacextend.TyTerminal
          ("MetaRocq",
           Vernacextend.TyTerminal
           ("Check",
            Vernacextend.TyTerminal ("Universes", Vernacextend.TyNil))),
          (let coqpp_body () =
            Vernactypes.vtmodifyprogram (fun ~pm -> (
# 10 "src/g_metarocq_loop_checking_plugin.mlg"
       Run_extractable.run_vernac check_universes 
            ) ~pm) in fun ?loc ~atts () ->
            coqpp_body (Attributes.unsupported_attributes atts)),
          None))]

