(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import BasicAst uGraph.
From MetaRocq.Template Require Import TemplateMonad TemplateMonad.Extractable.

(* Base types *)

Register bytestring.String.t as metarocq.string.type.
Register bytestring.String.EmptyString as metarocq.string.nil.
Register bytestring.String.String as metarocq.string.cons.

Register Corelib.Init.Byte.byte as metarocq.byte.type.

Register Corelib.Init.Datatypes.nat as metarocq.nat.type.
Register Corelib.Init.Datatypes.O as metarocq.nat.zero.
Register Corelib.Init.Datatypes.S as metarocq.nat.succ.

Register Corelib.Init.Datatypes.bool as metarocq.bool.type.
Register Corelib.Init.Datatypes.true as metarocq.bool.true.
Register Corelib.Init.Datatypes.false as metarocq.bool.false.

Register Corelib.Init.Datatypes.option as metarocq.option.type.
Register Corelib.Init.Datatypes.None as metarocq.option.none.
Register Corelib.Init.Datatypes.Some as metarocq.option.some.
Register MetaRocq.Template.TemplateMonad.Common.my_None as metarocq.option_instance.none.
Register MetaRocq.Template.TemplateMonad.Common.my_Some as metarocq.option_instance.some.

Register Corelib.Init.Datatypes.list as metarocq.list.type.
Register Corelib.Init.Datatypes.nil as metarocq.list.nil.
Register Corelib.Init.Datatypes.cons as metarocq.list.cons.

Register Corelib.Init.Datatypes.prod as metarocq.prod.type.
Register Corelib.Init.Datatypes.pair as metarocq.prod.intro.

Register Corelib.Init.Datatypes.sum as metarocq.sum.type.
Register Corelib.Init.Datatypes.inl as metarocq.sum.inl.
Register Corelib.Init.Datatypes.inr as metarocq.sum.inr.

Register Corelib.Init.Datatypes.unit as metarocq.unit.type.
Register Corelib.Init.Datatypes.tt as metarocq.unit.intro.

Register Corelib.Init.Specif.sigT as metarocq.sigma.type.
Register Corelib.Init.Specif.existT as metarocq.sigma.intro.
Register MetaRocq.Template.TemplateMonad.Common.existT_typed_term as metarocq.sigma.typed_term.

Register BinNums.positive as metarocq.pos.type.
Register BinNums.xI as metarocq.pos.xI.
Register BinNums.xO as metarocq.pos.xO.
Register BinNums.xH as metarocq.pos.xH.

Register BinNums.Z as metarocq.Z.type.
Register BinNums.Zpos as metarocq.Z.pos.
Register BinNums.Zneg as metarocq.Z.neg.
Register BinNums.Z0 as metarocq.Z.zero.

(* Ast *)
Register MetaRocq.Common.BasicAst.relevance as metarocq.ast.relevance.
Register MetaRocq.Common.BasicAst.Relevant as metarocq.ast.Relevant.
Register MetaRocq.Common.BasicAst.Irrelevant as metarocq.ast.Irrelevant.
Register MetaRocq.Common.BasicAst.mkBindAnn as metarocq.ast.mkBindAnn.
Register MetaRocq.Common.BasicAst.aname as metarocq.ast.aname.

Register MetaRocq.Common.BasicAst.nAnon as metarocq.ast.nAnon.
Register MetaRocq.Common.BasicAst.nNamed as metarocq.ast.nNamed.
Register MetaRocq.Common.Kernames.ident as metarocq.ast.ident.
Register MetaRocq.Common.Kernames.kername as metarocq.ast.kername.
Register MetaRocq.Common.Kernames.modpath as metarocq.ast.modpath.
Register MetaRocq.Common.Kernames.MPfile as metarocq.ast.MPfile.
Register MetaRocq.Common.Kernames.MPbound as metarocq.ast.MPbound.
Register MetaRocq.Common.Kernames.MPdot as metarocq.ast.MPdot.
Register MetaRocq.Common.Kernames.inductive as metarocq.ast.inductive.
Register MetaRocq.Common.Kernames.mkInd as metarocq.ast.mkInd.
Register MetaRocq.Common.Kernames.mkProjection as metarocq.ast.mkProjection.
Register MetaRocq.Common.Kernames.global_reference as metarocq.ast.global_reference.
Register MetaRocq.Common.Kernames.VarRef as metarocq.ast.VarRef.
Register MetaRocq.Common.Kernames.ConstRef as metarocq.ast.ConstRef.
Register MetaRocq.Common.Kernames.IndRef as metarocq.ast.IndRef.
Register MetaRocq.Common.Kernames.ConstructRef as metarocq.ast.ConstructRef.

Register MetaRocq.Common.BasicAst.name as metarocq.ast.name.
Register MetaRocq.Common.BasicAst.def as metarocq.ast.def.
Register MetaRocq.Common.BasicAst.mkdef as metarocq.ast.mkdef.
Register MetaRocq.Common.BasicAst.cast_kind as metarocq.ast.cast_kind.
Register MetaRocq.Common.BasicAst.case_info as metarocq.ast.case_info.
Register MetaRocq.Common.BasicAst.mk_case_info as metarocq.ast.mk_case_info.
Register MetaRocq.Common.BasicAst.VmCast as metarocq.ast.VmCast.
Register MetaRocq.Common.BasicAst.NativeCast as metarocq.ast.NativeCast.
Register MetaRocq.Common.BasicAst.Cast as metarocq.ast.Cast.
Register MetaRocq.Common.BasicAst.recursivity_kind as metarocq.ast.recursivity_kind.
Register MetaRocq.Common.BasicAst.Finite as metarocq.ast.Finite.
Register MetaRocq.Common.BasicAst.CoFinite as metarocq.ast.CoFinite.
Register MetaRocq.Common.BasicAst.BiFinite as metarocq.ast.BiFinite.
Register MetaRocq.Common.BasicAst.fresh_evar_id as metarocq.ast.fresh_evar_id.

(* Universes *)

Register MetaRocq.Common.Universes.allowed_eliminations as metarocq.ast.allowed_eliminations.
Register MetaRocq.Common.Universes.fresh_level as metarocq.ast.fresh_level.
Register MetaRocq.Common.Universes.fresh_universe as metarocq.ast.fresh_universe.
Register MetaRocq.Common.Universes.IntoSProp as metarocq.ast.IntoSProp.
Register MetaRocq.Common.Universes.IntoPropSProp as metarocq.ast.IntoPropSProp.
Register MetaRocq.Common.Universes.IntoSetPropSProp as metarocq.ast.IntoSetPropSProp.
Register MetaRocq.Common.Universes.IntoAny as metarocq.ast.IntoAny.
(* We convert from simple constraints to ones in Z *)
Register MetaRocq.Common.Universes.ConstraintType.Lt as metarocq.ast.constraints.Lt.
Register MetaRocq.Common.Universes.ConstraintType.Le0 as metarocq.ast.constraints.Le0.
Register MetaRocq.Common.Universes.ConstraintType.Le as metarocq.ast.constraints.Le.
Register MetaRocq.Common.Universes.ConstraintType.Eq as metarocq.ast.constraints.Eq.
Register MetaRocq.Common.Universes.Universe.t as metarocq.ast.universe.t.
Register MetaRocq.Common.Universes.Universe.make' as metarocq.ast.universe.make_of_level.
Register MetaRocq.Common.Universes.Universe.from_kernel_repr as metarocq.ast.universe.from_kernel_repr.
Register MetaRocq.Common.Universes.LevelSetProp.of_list as metarocq.ast.universe.of_list.
Register MetaRocq.Common.Universes.Level.t as metarocq.ast.level.t.
Register MetaRocq.Common.Universes.Level.level as metarocq.ast.level.Level.
Register MetaRocq.Common.Universes.PropLevel.t as metarocq.ast.level.prop_level_type.
Register MetaRocq.Common.Universes.PropLevel.lProp as metarocq.ast.level.lprop.
Register MetaRocq.Common.Universes.PropLevel.lSProp as metarocq.ast.level.lsprop.
Register MetaRocq.Common.Universes.Level.lzero as metarocq.ast.level.lzero.
Register MetaRocq.Common.Universes.Level.lvar as metarocq.ast.level.Var.

Register MetaRocq.Common.Universes.LevelExprSet.Mkt as metarocq.ast.levelexprset.mkt.
Register MetaRocq.Common.Universes.LevelExprSet.Build_nonEmptyLevelExprSet as metarocq.ast.universe.build0.
Register MetaRocq.Common.Universes.Sort.sSProp as metarocq.ast.sort.sprop.
Register MetaRocq.Common.Universes.Sort.sProp as metarocq.ast.sort.prop.
Register MetaRocq.Common.Universes.Sort.sType as metarocq.ast.sort.type.


Register MetaRocq.Common.Universes.Variance.t as metarocq.ast.variance.t.
Register MetaRocq.Common.Universes.Variance.Irrelevant as metarocq.ast.variance.Irrelevant.
Register MetaRocq.Common.Universes.Variance.Covariant as metarocq.ast.variance.Covariant.
Register MetaRocq.Common.Universes.Variance.Invariant as metarocq.ast.variance.Invariant.

Register MetaRocq.Common.Universes.universes_decl as metarocq.ast.universes_decl.
Register MetaRocq.Common.Universes.Monomorphic_ctx as metarocq.ast.Monomorphic_ctx.
Register MetaRocq.Common.Universes.Polymorphic_ctx as metarocq.ast.Polymorphic_ctx.

Register MetaRocq.Common.Universes.UnivConstraintSet.t_ as metarocq.ast.UnivConstraintSet.t_.
Register MetaRocq.Common.Universes.UnivConstraintSet.empty as metarocq.ast.UnivConstraintSet.empty.
Register MetaRocq.Common.Universes.UnivConstraintSet.add as metarocq.ast.UnivConstraintSet.add.
Register MetaRocq.Common.Universes.UnivConstraintSet.elements as metarocq.ast.UnivConstraintSet.elements.

Register MetaRocq.Common.Universes.UContext.t as metarocq.ast.UContext.t.
Register MetaRocq.Common.Universes.UContext.make as metarocq.ast.UContext.make.
Register MetaRocq.Common.Universes.AUContext.t as metarocq.ast.AUContext.t.
Register MetaRocq.Common.Universes.AUContext.make as metarocq.ast.AUContext.make.

Register MetaRocq.Common.Universes.LevelSet.t_ as metarocq.ast.LevelSet.t.
Register MetaRocq.Common.Universes.LevelSet.elements as metarocq.ast.LevelSet.elements.
Register MetaRocq.Common.Universes.UnivConstraint.make as metarocq.ast.make_univ_constraint.

Register MetaRocq.Common.uGraph.init_graph as metarocq.ast.graph.init.
(* FIXME wrong! *)
Register MetaRocq.Common.uGraph.gc_of_constraints as metarocq.ast.graph.add_global_constraints.

(* Terms *)

Register MetaRocq.Template.Ast.predicate as metarocq.ast.predicate.
Register MetaRocq.Template.Ast.mk_predicate as metarocq.ast.mk_predicate.
Register MetaRocq.Template.Ast.branch as metarocq.ast.branch.
Register MetaRocq.Template.Ast.mk_branch as metarocq.ast.mk_branch.

Register MetaRocq.Template.Ast.term as metarocq.ast.term.
Register MetaRocq.Template.Ast.tRel as metarocq.ast.tRel.
Register MetaRocq.Template.Ast.tVar as metarocq.ast.tVar.
Register MetaRocq.Template.Ast.tEvar as metarocq.ast.tEvar.
Register MetaRocq.Template.Ast.tSort as metarocq.ast.tSort.
Register MetaRocq.Template.Ast.tCast as metarocq.ast.tCast.
Register MetaRocq.Template.Ast.tProd as metarocq.ast.tProd.
Register MetaRocq.Template.Ast.tLambda as metarocq.ast.tLambda.
Register MetaRocq.Template.Ast.tLetIn as metarocq.ast.tLetIn.
Register MetaRocq.Template.Ast.tApp as metarocq.ast.tApp.
Register MetaRocq.Template.Ast.tConst as metarocq.ast.tConst.
Register MetaRocq.Template.Ast.tInd as metarocq.ast.tInd.
Register MetaRocq.Template.Ast.tConstruct as metarocq.ast.tConstruct.
Register MetaRocq.Template.Ast.tCase as metarocq.ast.tCase.
Register MetaRocq.Template.Ast.tProj as metarocq.ast.tProj.
Register MetaRocq.Template.Ast.tFix as metarocq.ast.tFix.
Register MetaRocq.Template.Ast.tCoFix as metarocq.ast.tCoFix.
Register MetaRocq.Template.Ast.tInt as metarocq.ast.tInt.
Register MetaRocq.Template.Ast.tFloat as metarocq.ast.tFloat.
Register MetaRocq.Template.Ast.tString as metarocq.ast.tString.
Register MetaRocq.Template.Ast.tArray as metarocq.ast.tArray.

(* Local and global declarations *)
Register MetaRocq.Template.Ast.parameter_entry as metarocq.ast.parameter_entry.
Register MetaRocq.Template.Ast.Build_parameter_entry as metarocq.ast.Build_parameter_entry.
Register MetaRocq.Template.Ast.definition_entry as metarocq.ast.definition_entry.
Register MetaRocq.Template.Ast.Build_definition_entry as metarocq.ast.Build_definition_entry.

Register MetaRocq.Common.Universes.Monomorphic_entry as metarocq.ast.Monomorphic_entry.
Register MetaRocq.Common.Universes.Polymorphic_entry as metarocq.ast.Polymorphic_entry.

Register MetaRocq.Template.Ast.constant_entry as metarocq.ast.constant_entry.
Register MetaRocq.Template.Ast.ParameterEntry as metarocq.ast.ParameterEntry.
Register MetaRocq.Template.Ast.DefinitionEntry as metarocq.ast.DefinitionEntry.

Register MetaRocq.Template.Ast.one_inductive_entry as metarocq.ast.one_inductive_entry.
Register MetaRocq.Template.Ast.Build_one_inductive_entry as metarocq.ast.Build_one_inductive_entry.
Register MetaRocq.Template.Ast.mutual_inductive_entry as metarocq.ast.mutual_inductive_entry.
Register MetaRocq.Template.Ast.Build_mutual_inductive_entry as metarocq.ast.Build_mutual_inductive_entry.

Register MetaRocq.Common.BasicAst.context_decl as metarocq.ast.context_decl.
Register MetaRocq.Common.BasicAst.mkdecl as metarocq.ast.mkdecl.
Register MetaRocq.Template.Ast.Env.context as metarocq.ast.context.

Register MetaRocq.Template.Ast.Env.constructor_body as metarocq.ast.constructor_body.
Register MetaRocq.Template.Ast.Env.Build_constructor_body as metarocq.ast.Build_constructor_body.
Register MetaRocq.Template.Ast.Env.Build_projection_body as metarocq.ast.Build_projection_body.
Register MetaRocq.Template.Ast.Env.projection_body as metarocq.ast.projection_body.
Register MetaRocq.Template.Ast.Env.one_inductive_body as metarocq.ast.one_inductive_body.
Register MetaRocq.Template.Ast.Env.Build_one_inductive_body as metarocq.ast.Build_one_inductive_body.
Register MetaRocq.Template.Ast.Env.mutual_inductive_body as metarocq.ast.mutual_inductive_body.
Register MetaRocq.Template.Ast.Env.Build_mutual_inductive_body as metarocq.ast.Build_mutual_inductive_body.
Register MetaRocq.Template.Ast.Env.constant_body as metarocq.ast.constant_body.
Register MetaRocq.Template.Ast.Env.Build_constant_body as metarocq.ast.Build_constant_body.

Register MetaRocq.Template.Ast.Env.global_decl as metarocq.ast.global_decl.
Register MetaRocq.Template.Ast.Env.ConstantDecl as metarocq.ast.ConstantDecl.
Register MetaRocq.Template.Ast.Env.InductiveDecl as metarocq.ast.InductiveDecl.
Register MetaRocq.Common.Environment.Retroknowledge.mk_retroknowledge as metarocq.ast.mk_retroknowledge.
Register MetaRocq.Template.Ast.Env.mk_global_env as metarocq.ast.Build_global_env.
Register MetaRocq.Template.Ast.Env.global_env as metarocq.ast.global_env.
Register MetaRocq.Template.Ast.Env.global_env_ext as metarocq.ast.global_env_ext.
Register MetaRocq.Template.Ast.Env.program as metarocq.ast.program.

(* Template monad *)

Register MetaRocq.Template.TemplateMonad.Common.cbv as metarocq.template.cbv.
Register MetaRocq.Template.TemplateMonad.Common.cbn as metarocq.template.cbn.
Register MetaRocq.Template.TemplateMonad.Common.hnf as metarocq.template.hnf.
Register MetaRocq.Template.TemplateMonad.Common.all as metarocq.template.all.
Register MetaRocq.Template.TemplateMonad.Common.lazy as metarocq.template.lazy.
Register MetaRocq.Template.TemplateMonad.Common.unfold as metarocq.template.unfold.

Register MetaRocq.Template.TemplateMonad.Common.local as metarocq.template.hints.local.
Register MetaRocq.Template.TemplateMonad.Common.export as metarocq.template.hints.export.
Register MetaRocq.Template.TemplateMonad.Common.global as metarocq.template.hints.global.


(* Prop *)
Register MetaRocq.Template.TemplateMonad.Core.tmReturn as metarocq.templatemonad.prop.tmReturn.
Register MetaRocq.Template.TemplateMonad.Core.tmBind as metarocq.templatemonad.prop.tmBind.
Register MetaRocq.Template.TemplateMonad.Core.tmPrint as metarocq.templatemonad.prop.tmPrint.
Register MetaRocq.Template.TemplateMonad.Core.tmMsg as metarocq.templatemonad.prop.tmMsg.
Register MetaRocq.Template.TemplateMonad.Core.tmFail as metarocq.templatemonad.prop.tmFail.
Register MetaRocq.Template.TemplateMonad.Core.tmEval as metarocq.templatemonad.prop.tmEval.
Register MetaRocq.Template.TemplateMonad.Core.tmVariable as metarocq.templatemonad.prop.tmVariable.
Register MetaRocq.Template.TemplateMonad.Core.tmLemma as metarocq.templatemonad.prop.tmLemma.
Register MetaRocq.Template.TemplateMonad.Core.tmDefinitionRed_ as metarocq.templatemonad.prop.tmDefinitionRed_.
Register MetaRocq.Template.TemplateMonad.Core.tmAxiomRed as metarocq.templatemonad.prop.tmAxiomRed.
Register MetaRocq.Template.TemplateMonad.Core.tmMkDefinition as metarocq.templatemonad.prop.tmMkDefinition.
Register MetaRocq.Template.TemplateMonad.Core.tmMkInductive as metarocq.templatemonad.prop.tmMkInductive.
Register MetaRocq.Template.TemplateMonad.Core.tmFreshName as metarocq.templatemonad.prop.tmFreshName.
Register MetaRocq.Template.TemplateMonad.Core.tmLocate as metarocq.templatemonad.prop.tmLocate.
Register MetaRocq.Template.TemplateMonad.Core.tmLocateModule as metarocq.templatemonad.prop.tmLocateModule.
Register MetaRocq.Template.TemplateMonad.Core.tmLocateModType as metarocq.templatemonad.prop.tmLocateModType.
Register MetaRocq.Template.TemplateMonad.Core.tmCurrentModPath as metarocq.templatemonad.prop.tmCurrentModPath.

Register MetaRocq.Template.TemplateMonad.Core.tmQuote as metarocq.templatemonad.prop.tmQuote.
Register MetaRocq.Template.TemplateMonad.Core.tmQuoteRec as metarocq.templatemonad.prop.tmQuoteRec.
Register MetaRocq.Template.TemplateMonad.Core.tmQuoteRecTransp as metarocq.templatemonad.prop.tmQuoteRecTransp.
Register MetaRocq.Template.TemplateMonad.Core.tmQuoteInductive as metarocq.templatemonad.prop.tmQuoteInductive.
Register MetaRocq.Template.TemplateMonad.Core.tmQuoteConstant as metarocq.templatemonad.prop.tmQuoteConstant.
Register MetaRocq.Template.TemplateMonad.Core.tmQuoteUniverses as metarocq.templatemonad.prop.tmQuoteUniverses.
Register MetaRocq.Template.TemplateMonad.Core.tmQuoteModule as metarocq.templatemonad.prop.tmQuoteModule.
Register MetaRocq.Template.TemplateMonad.Core.tmQuoteModFunctor as metarocq.templatemonad.prop.tmQuoteModFunctor.
Register MetaRocq.Template.TemplateMonad.Core.tmQuoteModType as metarocq.templatemonad.prop.tmQuoteModType.

Register MetaRocq.Template.TemplateMonad.Core.tmUnquote as metarocq.templatemonad.prop.tmUnquote.
Register MetaRocq.Template.TemplateMonad.Core.tmUnquoteTyped as metarocq.templatemonad.prop.tmUnquoteTyped.

Register MetaRocq.Template.TemplateMonad.Core.tmInferInstance as metarocq.templatemonad.prop.tmInferInstance.
Register MetaRocq.Template.TemplateMonad.Core.tmExistingInstance as metarocq.templatemonad.prop.tmExistingInstance.

Register MetaRocq.Template.TemplateMonad.Core.tmTestQuote as metarocq.templatemonad.prop.tmTestQuote.
Register MetaRocq.Template.TemplateMonad.Core.tmTestUnquote as metarocq.templatemonad.prop.tmTestUnquote.
Register MetaRocq.Template.TemplateMonad.Core.tmQuoteDefinition as metarocq.templatemonad.prop.tmQuoteDefinition.
Register MetaRocq.Template.TemplateMonad.Core.tmQuoteDefinitionRed as metarocq.templatemonad.prop.tmQuoteDefinitionRed.
Register MetaRocq.Template.TemplateMonad.Core.tmQuoteRecDefinition as metarocq.templatemonad.prop.tmQuoteRecDefinition.


(* Type *)
Register MetaRocq.Template.TemplateMonad.Extractable.tmReturn as metarocq.templatemonad.type.tmReturn.
Register MetaRocq.Template.TemplateMonad.Extractable.tmBind as metarocq.templatemonad.type.tmBind.
Register MetaRocq.Template.TemplateMonad.Extractable.tmPrint as metarocq.templatemonad.type.tmPrint.
Register MetaRocq.Template.TemplateMonad.Extractable.tmMsg as metarocq.templatemonad.type.tmMsg.
Register MetaRocq.Template.TemplateMonad.Extractable.tmFail as metarocq.templatemonad.type.tmFail.
Register MetaRocq.Template.TemplateMonad.Extractable.tmEval as metarocq.templatemonad.type.tmEval.
Register MetaRocq.Template.TemplateMonad.Extractable.tmDefinition_ as metarocq.templatemonad.type.tmDefinition_.
Register MetaRocq.Template.TemplateMonad.Extractable.tmAxiom as metarocq.templatemonad.type.tmAxiom.
Register MetaRocq.Template.TemplateMonad.Extractable.tmLemma as metarocq.templatemonad.type.tmLemma.
Register MetaRocq.Template.TemplateMonad.Extractable.tmFreshName as metarocq.templatemonad.type.tmFreshName.
Register MetaRocq.Template.TemplateMonad.Extractable.tmLocate as metarocq.templatemonad.type.tmLocate.
Register MetaRocq.Template.TemplateMonad.Extractable.tmLocateModule as metarocq.templatemonad.type.tmLocateModule.
Register MetaRocq.Template.TemplateMonad.Extractable.tmLocateModType as metarocq.templatemonad.type.tmLocateModType.
Register MetaRocq.Template.TemplateMonad.Extractable.tmCurrentModPath as metarocq.templatemonad.type.tmCurrentModPath.
Register MetaRocq.Template.TemplateMonad.Extractable.tmQuoteInductive as metarocq.templatemonad.type.tmQuoteInductive.
Register MetaRocq.Template.TemplateMonad.Extractable.tmQuoteUniverses as metarocq.templatemonad.type.tmQuoteUniverses.
Register MetaRocq.Template.TemplateMonad.Extractable.tmQuoteConstant as metarocq.templatemonad.type.tmQuoteConstant.
Register MetaRocq.Template.TemplateMonad.Extractable.tmQuoteModule as metarocq.templatemonad.type.tmQuoteModule.
Register MetaRocq.Template.TemplateMonad.Extractable.tmQuoteModFunctor as metarocq.templatemonad.type.tmQuoteModFunctor.
Register MetaRocq.Template.TemplateMonad.Extractable.tmQuoteModType as metarocq.templatemonad.type.tmQuoteModType.
Register MetaRocq.Template.TemplateMonad.Extractable.tmInductive as metarocq.templatemonad.type.tmInductive.
Register MetaRocq.Template.TemplateMonad.Extractable.tmInferInstance as metarocq.templatemonad.type.tmInferInstance.
Register MetaRocq.Template.TemplateMonad.Extractable.tmExistingInstance as metarocq.templatemonad.type.tmExistingInstance.
