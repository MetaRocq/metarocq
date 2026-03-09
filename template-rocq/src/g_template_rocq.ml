let _ = Mltop.add_known_module "rocq-metarocq-template-rocq.plugin"

# 4 "src/g_template_rocq.mlg"
 

open Attributes
open Ltac_plugin
open Names

(** Calling Ltac **)

let ltac_lcall tac args =
  let (location, name) = Loc.tag (Names.Id.of_string tac)
    (* Loc.tag @@ Names.Id.of_string tac *)
  in
  CAst.make ?loc:location (Tacexpr.TacArg(Tacexpr.TacCall
                              (CAst.make (Locus.ArgVar (CAst.make ?loc:location name),args))))

open Tacexpr
open Tacinterp
open Stdarg
open Tacarg
open Redexpr

(* If strict unquote universe mode is on then fail when unquoting a non *)
(* declared universe / an empty list of level expressions. *)
(* Otherwise, add it / a fresh level the global environnment. *)

let _ =
  let open Goptions in
  declare_bool_option
    { optdepr  = None;
      optstage = Interp;
      optkey   = ["MetaRocq"; "Strict"; "Unquote"; "Universe"; "Mode"];
      optread  = (fun () -> !Denoter.strict_unquote_universe_mode);
      optwrite = (fun b -> Denoter.strict_unquote_universe_mode := b) }

let ltac_apply (f : Value.t) (args: Tacinterp.Value.t list) =
  let fold arg (i, vars, lfun) =
    let id = Names.Id.of_string ("x" ^ string_of_int i) in
    let (l,n) = (Loc.tag id) in
    let x = Reference (Locus.ArgVar (CAst.make ?loc:l n)) in
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let lfun = Id.Map.add (Id.of_string "F") f lfun in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Tacinterp.eval_tactic_ist ist (ltac_lcall "F" args)

let to_ltac_val c = Tacinterp.Value.of_constr c

let run_template_program ~pm env evm ~poly pgm =
  Run_template_monad.run_template_program_rec ~poly (fun ~st _ _ _ -> st) ~st:pm env (evm, pgm)

let fresh_env () =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  env, sigma

let to_constr_evars sigma c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c


let () = Vernacextend.static_vernac_extend ~plugin:(Some "rocq-metarocq-template-rocq.plugin") ~command:"TemplateRocq_Test_Quote" ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML
         (false,
          Vernacextend.TyTerminal
          ("MetaRocq",
           Vernacextend.TyTerminal
           ("Test",
            Vernacextend.TyTerminal
            ("Quote",
             Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr),
             Vernacextend.TyNil)))),
          (let coqpp_body def poly =
            Vernactypes.vtmodifyprogram (fun ~pm -> (
# 67 "src/g_template_rocq.mlg"
        fun ~pm -> let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmTestQuote) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm,
          [|Constr.mkRel 0; to_constr_evars evm def|]) in
        run_template_program ~pm env evm ~poly pgm 
            ) ~pm) in fun def ?loc ~atts () ->
            coqpp_body def (Attributes.parse 
# 66 "src/g_template_rocq.mlg"
                 polymorphic
               atts)),
          None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "rocq-metarocq-template-rocq.plugin") ~command:"TemplateRocq_Quote_Definition" ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML
         (false,
          Vernacextend.TyTerminal
          ("MetaRocq",
           Vernacextend.TyTerminal
           ("Quote",
            Vernacextend.TyTerminal
            ("Definition",
             Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident),
             Vernacextend.TyTerminal
             (":=",
              Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr),
              Vernacextend.TyNil)))))),
          (let coqpp_body name def poly =
            Vernactypes.vtmodifyprogram (fun ~pm -> (
# 77 "src/g_template_rocq.mlg"
        fun ~pm -> let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmQuoteDefinition) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr_quoter.quote_ident name; Constr.mkRel 0;
          to_constr_evars evm def|]) in
        run_template_program ~pm env evm ~poly pgm 
            ) ~pm) in fun name def ?loc ~atts () ->
            coqpp_body name def (Attributes.parse 
# 76 "src/g_template_rocq.mlg"
                 polymorphic
               atts)),
          None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "rocq-metarocq-template-rocq.plugin") ~command:"TemplateRocq_Quote_Definition_Eval" ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML
         (false,
          Vernacextend.TyTerminal
          ("MetaRocq",
           Vernacextend.TyTerminal
           ("Quote",
            Vernacextend.TyTerminal
            ("Definition",
             Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident),
             Vernacextend.TyTerminal
             (":=",
              Vernacextend.TyTerminal
              ("Eval",
               Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_red_expr),
               Vernacextend.TyTerminal
               ("in",
                Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                Vernacextend.TyNil))))))))),
          (let coqpp_body name rd def poly =
            Vernactypes.vtmodifyprogram (fun ~pm -> (
# 87 "src/g_template_rocq.mlg"
        fun ~pm -> let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        (* TODO : implem quoting of tactic reductions so that we can use ptmQuoteDefinitionRed *)
        let (evm, rd) = Redexpr.interp_redexp_no_ltac env evm rd in
	      let (evm, def) = Plugin_core.reduce env evm rd (to_constr_evars evm def) in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmQuoteDefinition) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr_quoter.quote_ident name; Constr.mkRel 0; def|]) in
        run_template_program ~pm env evm ~poly pgm 
            ) ~pm) in fun name rd def ?loc ~atts () ->
            coqpp_body name rd def (Attributes.parse 
# 86 "src/g_template_rocq.mlg"
               polymorphic
               atts)),
          None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "rocq-metarocq-template-rocq.plugin") ~command:"TemplateRocq_Quote_Recursively_Definition" ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML
         (false,
          Vernacextend.TyTerminal
          ("MetaRocq",
           Vernacextend.TyTerminal
           ("Quote",
            Vernacextend.TyTerminal
            ("Recursively",
             Vernacextend.TyTerminal
             ("Definition",
              Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident),
              Vernacextend.TyTerminal
              (":=",
               Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr),
               Vernacextend.TyNil))))))),
          (let coqpp_body name def poly =
            Vernactypes.vtmodifyprogram (fun ~pm -> (
# 99 "src/g_template_rocq.mlg"
        fun ~pm -> let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmQuoteRecDefinition) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr_quoter.quote_ident name; Constr.mkRel 0;
          to_constr_evars evm def|]) in
        run_template_program ~pm env evm ~poly pgm 
            ) ~pm) in fun name def ?loc ~atts () ->
            coqpp_body name def (Attributes.parse 
# 98 "src/g_template_rocq.mlg"
               polymorphic
               atts)),
          None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "rocq-metarocq-template-rocq.plugin") ~command:"TemplateRocq_Test_Unquote" ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML
         (false,
          Vernacextend.TyTerminal
          ("MetaRocq",
           Vernacextend.TyTerminal
           ("Test",
            Vernacextend.TyTerminal
            ("Unquote",
             Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr),
             Vernacextend.TyNil)))),
          (let coqpp_body def poly =
            Vernactypes.vtmodifyprogram (fun ~pm -> (
# 109 "src/g_template_rocq.mlg"
        fun ~pm -> let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmTestUnquote) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm,
          [|to_constr_evars evm def|]) in
        run_template_program ~pm env evm ~poly pgm 
            ) ~pm) in fun def ?loc ~atts () ->
            coqpp_body def (Attributes.parse 
# 108 "src/g_template_rocq.mlg"
                 polymorphic
               atts)),
          None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "rocq-metarocq-template-rocq.plugin") ~command:"TemplateRocq_Make_Definition" ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML
         (false,
          Vernacextend.TyTerminal
          ("MetaRocq",
           Vernacextend.TyTerminal
           ("Unquote",
            Vernacextend.TyTerminal
            ("Definition",
             Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident),
             Vernacextend.TyTerminal
             (":=",
              Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr),
              Vernacextend.TyNil)))))),
          (let coqpp_body name def poly =
            Vernactypes.vtmodifyprogram (fun ~pm -> (
# 119 "src/g_template_rocq.mlg"
        fun ~pm -> let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmMkDefinition) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm,
          [|Constr_quoter.quote_ident name;
            to_constr_evars evm def|]) in
        run_template_program ~pm env evm ~poly pgm 
            ) ~pm) in fun name def ?loc ~atts () ->
            coqpp_body name def (Attributes.parse 
# 118 "src/g_template_rocq.mlg"
               polymorphic
               atts)),
          None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "rocq-metarocq-template-rocq.plugin") ~command:"TemplateRocq_Make_Inductive" ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML
         (false,
          Vernacextend.TyTerminal
          ("MetaRocq",
           Vernacextend.TyTerminal
           ("Unquote",
            Vernacextend.TyTerminal
            ("Inductive",
             Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr),
             Vernacextend.TyNil)))),
          (let coqpp_body def poly =
            Vernactypes.vtmodifyprogram (fun ~pm -> (
# 130 "src/g_template_rocq.mlg"
        fun ~pm -> let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmMkInductive) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm,
          [|Constr_quoter.quote_bool false; to_constr_evars evm def|]) in
        run_template_program ~pm env evm ~poly pgm 
            ) ~pm) in fun def ?loc ~atts () ->
            coqpp_body def (Attributes.parse 
# 129 "src/g_template_rocq.mlg"
               polymorphic
               atts)),
          None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "rocq-metarocq-template-rocq.plugin") ~command:"TemplateRocq_Run_Template_Program" ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML
         (false,
          Vernacextend.TyTerminal
          ("MetaRocq",
           Vernacextend.TyTerminal
           ("Run",
            Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr),
            Vernacextend.TyNil))),
          (let coqpp_body def poly =
            Vernactypes.vtmodifyprogram (fun ~pm -> (
# 140 "src/g_template_rocq.mlg"
        fun ~pm -> let (env, evm) = fresh_env () in
        let (pgm, ctx) = Constrintern.interp_constr env evm def in
        let evm = Evd.from_ctx ctx in
        let pgm = EConstr.to_constr ~abort_on_undefined_evars:true evm pgm in
        run_template_program ~pm env evm ~poly pgm 
            ) ~pm) in fun def ?loc ~atts () ->
            coqpp_body def (Attributes.parse 
# 139 "src/g_template_rocq.mlg"
               polymorphic
               atts)),
          None))]

let () = Tacentries.tactic_extend "rocq-metarocq-template-rocq.plugin" "TemplateRocq_quote_term" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("quote_term", Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                              Tacentries.TyNil))), 
           (fun c tac ist -> 
# 152 "src/g_template_rocq.mlg"
        (* quote the given term, pass the result to t *)
        Proofview.Goal.enter begin fun gl ->
          let env = Proofview.Goal.env gl in
          let sigma = Proofview.Goal.sigma gl in
          let c = to_constr_evars sigma c in
          let c = Constr_quoter.quote_term env sigma c in
          ltac_apply tac (List.map to_ltac_val [EConstr.of_constr c])
  end 
           )))]

let () = Tacentries.tactic_extend "rocq-metarocq-template-rocq.plugin" "TemplateRocq_denote_term" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("denote_term", Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                               Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                               Tacentries.TyNil))), 
           (fun c tac ist -> 
# 164 "src/g_template_rocq.mlg"
        Proofview.Goal.enter (begin fun gl ->
         let env = Proofview.Goal.env gl in
         let evm = Proofview.Goal.sigma gl in
         let evm, c = Constr_denoter.denote_term env evm (to_constr_evars evm c) in
         let evm, _ = Typing.type_of env evm (EConstr.of_constr c) in
         Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evm)
	   (ltac_apply tac (List.map to_ltac_val [EConstr.of_constr c]))
      end) 
           )))]

let () = Tacentries.tactic_extend "rocq-metarocq-template-rocq.plugin" "TemplateRocq_run_template_program" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("run_template_program", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                            Tacentries.TyNil))), (fun c tac ist -> 
# 176 "src/g_template_rocq.mlg"
        let open Proofview.Notations in
        Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (name, poly) ->
        Proofview.Goal.enter (begin fun gl ->
         let env = Proofview.Goal.env gl in
         let evm = Proofview.Goal.sigma gl in
         let ret = ref None in
         (* We don't allow opening obligations / updating the vernacular inside proofs / as tactics *)
         let pm = Declare.OblState.empty in
         let _pm = Run_template_monad.run_template_program_rec
             ~poly ~intactic:true ~st:pm (fun ~st env evm t -> ret := Some (env,evm,t); st)
             env (evm, to_constr_evars evm c)
         in
         match !ret with
         | Some (env, evm, t) ->
            Proofview.tclTHEN
              (Proofview.Unsafe.tclEVARS evm)
              (ltac_apply tac (List.map to_ltac_val [EConstr.of_constr t]))
         | None -> Proofview.tclUNIT ()
       end) 
                                                 )))]

