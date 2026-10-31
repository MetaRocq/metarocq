# PCUIC

## General

| File                | Description
|---------------------|----------------------------------------------
| [PCUICUtils]        | Generally useful definitions and properties
| [PCUICOnOne]        | Lemmas for the OnOne relation
| [PCUICPrimitive]    | Definitions and lemmas for primitives datatypes
| [PCUICTactics]      | Tactics used throughout the library
| [Extraction]        | Setup to extract the development



[PCUICUtils]: ./utils/PCUICUtils.v
[PCUICOnOne]: ./utils/PCUICOnOne.v
[PCUICPrimitive]: ./utils/PCUICPrimitive.v
[PCUICTactics]: ./Syntax/PCUICTactics.v
[Extraction]: Extraction.v

## AST

| File             | Description
|------------------|----------------------------------------------
| [PCUICAst]       | Definition of the Abstract Syntax Tree of PCUIC
| [PCUICAstUtils]  | General utilities on the AST
| [PCUICCases]     | Utilities for the case representation
| [PCUICInduction] | Induction principle on syntax
| [PCUICSize]      | Size of terms
| [PCUICDepth]     | Depth of terms
| [PCUICReflect]   | Decidability of equality between terms
| [PCUICContextRelations] | Helper lemmas for relations between contexts
| [PCUICPosition]  | Notions of position and stack, well-order on positions

[PCUICAst]: PCUICAst.v
[PCUICAstUtils]: ./utils/PCUICAstUtils.v
[PCUICCases]: ./Syntax/PCUICCases.v
[PCUICInduction]: ./Syntax/PCUICInduction.v
[PCUICSize]: ./utils/PCUICSize.v
[PCUICDepth]: ./Syntax/PCUICDepth.v
[PCUICReflect]: ./Syntax/PCUICReflect.v
[PCUICContextRelations]: ./Syntax/PCUICContextRelations.v
[PCUICPosition]: ./Syntax/PUICPosition.v


## Universes and global environment

| File                | Description                                               |
|---------------------|-----------------------------------------------------------|
| [PCUICGlobalEnv]    | Generic properties of global environments
| [PCUICWfUniverses]  | Definition and properties of a predicate saying that the universe levels of a term are in the global environment

[PCUICGlobalEnv]: ./PCUICGlobalEnv.v
[PCUICWfUniverses]: ./PCUICWfUniverses.v


## Closedness, Renamings and Instantiations

| File                  | Description
|-----------------------|-------------------------------------------------------
| [PCUICUnivSubst]      | Substitution of universe variables (for universe polymorphism)
| [PCUICLiftSubst]      | First commutation properties for lifting and substitution
| [PCUICSigmaCalculus]  | General theory of renamings
| [PCUICClosed]         | Properties of the closedness predicate on terms
| [PCUICOnFreeVars]     | General theory of predicates on (free) variables (generalizing closedness)
| [PCUICRenameDef]      | Definition of well-behaved renamings
| [PCUICInstDef]        | Definition of well-behaved instantiations
| [PCUICContextSubst]   | Linking a context (with let-ins), an instance (reversed substitution) for its assumptions and a well-formed substitution for it

[PCUICUnivSubst]: ./Syntax/PCUICUnivSubst.v
[PCUICLiftSubst]: ./Syntax/PCUICLiftSubst.v
[PCUICSigmaCalculus]: ./PCUICSigmaCalculus.v
[PCUICClosed]: ./Syntax/PCUICClosed.v
[PCUICOnFreeVars]: ./Syntax/PCUICOnFreeVars.v
[PCUICRenameDef]: ./Syntax/PCUICRenameDef.v
[PCUICInstDef]: ./Syntax/PCUICRenameDef.v
[PCUICContextSubst]: ./PCUICContextSubst.v


## Nameless terms

| File                | Description                                               |
|---------------------|-----------------------------------------------------------|
| [PCUICNamelessDef]  | Name-removing translation
| [PCUICNamelessConv] | Conversion is insensible to names
| [PCUICNamelessTyp]  | Typing is insensible to names

[PCUICNamelessDef]: ./Syntax/NamelessDef.v
[PCUICNamelessConv]: ./Conversion/PCUICNamelessConv.v
[PCUICNamelessTyp]: ./Typing/PCUICNamelessTyp.v


## Equality up to universes

| File                  | Description
| ----------------------| --------------------
| [PCUICEquality]       | Equality up to universes between terms (`eq_term`)
| [PCUICCasesContexts]  | Helper lemmas for the handling of case branche and predicate contexts
| [PCUICEqualityDec]    | Decidability of equality up to universes

[PCUICCasesContexts]: ./PCUICCasesContexts.v
[PCUICEquality]: ./PCUICEquality.v
[PCUICEqualityDec]: ./PCUICEqualityDec.v


## Reduction

| File                  | Description
| ----------------------| --------------------
| [PCUICReduction]      | Definition of reduction and proof of congruence lemmas
| [PCUICContextReduction] | Properties of reduction between contexts
| [PCUICParallelReduction] | Definition of parallel reduction, and stability by weakening and substitution
| [PCUICParallelReductionConfluence] | Proof of the diamond property for parallel reduction
| [PCUICConfluence] | Proof of confluence for reduction and that equality up to universes is a simulation for reduction
| [PCUICRedTypeIrrelevance] | Types and names in the context are irrelevant for reduction, only the bodies of definitions are used


[PCUICReduction]: ./PCUICReduction.v
[PCUICContextReduction]: ./PCUICContextReduction.v
[PCUICParallelReduction]: ./PCUICParallelReduction.v
[PCUICParallelReductionConfluence]: ./PCUICParallelReductionConfluence.v
[PCUICConfluence]: ./PCUICConfluence.v
[PCUICRedTypeIrrelevance]: ./PCUICRedTypeIrrelevance.v


## Conversion/Cumulativity

| File                  | Description
| ----------------------| --------------------
| [PCUICCumulativitySpec] | Definition of declarative cumulativity used to define typing
| [PCUICCumulativity] | Definition of algorithmic cumulativity (reduction to terms equal up to universes)
| [PCUICWellScopedCumulativity] | Definition of cumulativity restricted to well-scoped terms, which is transitive
| [PCUICContextConversion] | Properties of the lifting of reduction and conversions to contexts
| [PCUICConversion] | High-level properties of conversions: congruence and inversion lemmas, equivalence between algorithmic and declarative one…

[PCUICCumulativitySpec]: ./PCUICCumulativitySpec.v
[PCUICCumulativity]: ./PCUICCumulativity.v
[PCUICWellScopedCumulativity]: ./PCUICWellScopedCumulativity.v
[PCUICContextConversion]: ./PCUICContextConversion.v
[PCUICConversion]: ./PCUICConversion.v


## Typing

| File                | Description                                               |
|---------------------|-----------------------------------------------------------|
| [PCUICTyping]       | Definition of typing
| [PCUICGeneration]   | Derived typing rules for e.g. iterated application
| [PCUICClosedTyp]    | Well-typed terms are closed, and various consequences
| [PCUICInversion]    | Inversion lemmas on typing

[PCUICTyping]: ./PCUICTyping.v
[PCUICGeneration]: ./PCUICGeneration.v
[PCUICInversion]: ./PCUICInversion.v
[PCUICClosedTyp]: ./Typing/PCUICClosedTyp.v


## Stability of Conversion/Cumulativity

| File                | Description                                               |
|---------------------|-----------------------------------------------------------|
| [PCUICRenameConv]   | Stability of conversion/cumulativity by renaming
| [PCUICWeakeningConv] | Stability of conversion/cumulativity by extension of the local context (special case of renaming)
| [PCUICInstConv]     | Stability of conversion/cumulativity by instantiation
| [PCUICWeakeningEnvConv] | Stability of conversion/cumulativity by global environment extension
| [PCUICUnivSubstitutionConv] | Stability of conversion/cumulativity by substitution of universe variables
| [PCUICClosedConv] | Helper lemmas on the closedness predicate
| [PCUICOnFreeVarsConv] | Helper lemmas for renamings and free variables

[PCUICRenameConv]: ./Conversion/PCUICRenameConv.v
[PCUICWeakeningConv]: ./Conversion/PCUICWeakeningConv.v
[PCUICInstConv]: ./Conversion/PCUICInstConv.v
[PCUICWeakeningEnvConv]: ./Conversion/PCUICWeakeningEnvConv.v
[PCUICUnivSubstitutionConv]: ./Conversion/PCUICUnivSubstitutionConv.v
[PCUICClosedConv]: ./Conversion/PCUICClosedConv.v
[PCUICOnFreeVarsConv]: ./Conversion/PCUICOnFreeVarsConv.v


## Stability of Typing

| File                | Description                                               |
|---------------------|-----------------------------------------------------------|
| [PCUICGuardCondition]| Axioms on the stability of the guard condition
| [PCUICRenameTyp]    | Stability of typing by renaming
| [PCUICWeakeningTyp] | Stability of typing by extension of the local context (special case of renaming)
| [PCUICInstTyp]      | Stability of typing by instatiation
| [PCUICSubstitution] | Stability of typing by substitution (derived as a special case of stability by instantiation)
| [PCUICWeakeningEnvTyp] | Stability of typing by extension of the global environment
| [PCUICUnivSubstitutionTyp] | Stability of typing by substitution of universe levels
| [PCUICConversionTyp] | Stability of typing by cumulativity of the local context

[PCUICGuardCondition]: ./PCUICGuardCondition.v
[PCUICRenameTyp]: ./Typing/PCUICRenameTyp.v
[PCUICWeakeningTyp]: ./Typing/PCUICWeakeningTyp.v
[PCUICInstTyp]: ./Typing/PCUICInstTyp.v
[PCUICSubstitution]: ./PCUICSubstitution.v
[PCUICWeakeningEnvTyp]: ./Typing/PCUICWeakeningEnvTyp.v
[PCUICUnivSubstitutionTyp]: Typing/PCUICUnivSubstitutionTyp.v
[PCUICConversionTyp]: Typing/PCUICContextConversionTyp.v


## Metatheoretical properties of typing

| File              | Description
|-------------------|----------------------------------------------------
| [PCUICContexts]     | Various properties on contexts
| [PCUICArities]    | Properties on lists of terms
| [PCUICSpine]      | Properties on spines (lists of terms) relating to typing, substitutions, and so on
| [PCUICInductives] | Technical typing and conversion lemmas related to inductive definitions
| [PCUICValidity] | Every term `A` such that `Γ ⊢ t : A` is a type
| [PCUICInductiveInversion] | Typing properties and inversions for inductive types, constructors and projections
| [PCUICAlpha] | Typing does not depend on names
| [PCUICSR]    | Subject reduction: typing is preserved by reduction
| [PCUICPrincipality] | Existence of a least type for any typable term

[PCUICContexts]: ./PCUICContexts.v
[PCUICArities]: ./PCUICArities.v
[PCUICSpine]: ./PCUICSpine.v
[PCUICInductives]: ./PCUICInductives.v
[PCUICValidity]: ./PCUICValidity.v
[PCUICInductiveInversion]: ./PCUICInductiveInversion.v
[PCUICAlpha]: ./PCUICAlpha.v
[PCUICSR]: ./PCUICSR.v
[PCUICPrincipality]: ./PCUICPrincipality.v


## Bidirectional Typing
| File               | Description                                             |
|--------------------|---------------------------------------------------------|
| [BDTyping]         | Bidirectional typing derivation and its induction principle
| [BDToPCUIC]        | Bidirectional typing implies undirected typing
| [BDFromPCUIC]      | Undirected typing implies bidirectional typing
| [BDUnique]         | Inferred types are unique (up to reductions)
| [BDStrengthening]  | Bidirectional typing can be strengthened (variables not appearing in a term can be removed from the context while keeping typability)

[BDTyping]: ./Bidirectional/BDTyping.v
[BDToPCUIC]: ./Bidirectional/BDToPCUIC.v
[BDFromPCUIC]: ./Bidirectional/BDFromPCUIC.v
[BDUnique]: ./Bidirectional/BDUnique.v
[BDStrengthening]: ./Bidirectional/BDStrengthening.v



## Preliminaries for Safe Checker

| File               | Description                                             |
|--------------------|---------------------------------------------------------|
| [PCUICNormal]      | (Weak-head) neutral and normal forms                    |
| [PCUICSafelemmas] | Lemma-base for the safe checker                         |
| [PCUICConvCumInversion] | Definition of the relation used as specification by the safe conversion function
| [PCUICSN]          | Axiom of normalization                                  |

[PCUICNormal]: ./PCUICNormal.v
[PCUICSafelemmas]: ./PCUICSafelemmas.v
[PCUICSN]: ./PCUICSN.v
[PCUICConvCumInversion]: ./PCUICConvCumInversion.v


## Preliminaries for Erasure

| File               | Description                                             |
|--------------------|---------------------------------------------------------|
| [PCUICCSubst]      | Definition of closed (capturing) substitution             |
| [PCUICWcbvEval]    | Weak-head call-by-value evaluation strategy
| [PCUICCanonicity]  | Lemmas around reduction and evaluation
| [PCUICCumulProp]   | Definition and properties of the `cumul_prop` relation, relating two terms convertible up to type levels
| [PCUICElimination] | Properties of the singleton elimination criterion for propositional inductive types
| [PCUICExpandLets] | Expansion of let-bindings in constructor arguments
| [PCUICExpandLetsCorrectness] | Expansion of let-bindings preserves typing

[PCUICCSubst]: ./PCUICCSubst.v
[PCUICWcbvEval]: ./PCUICWcbvEval.v
[PCUICCanonicity]: ./PCUICCanonicity.v
[PCUICCumulProp]: ./PCUICCumulProp.v
[PCUICElimination]: ./PCUICElimination.v
[PCUICExpandLets]: ./PCUICExpandLets.v
[PCUICExpandLetsCorrectness]: ./PCUICExpandLetsCorrectness.v


## Relation with Template-Rocq

| File              | Description                                              |
|-------------------|----------------------------------------------------------|
| [TemplateToPCUIC] | Translation from Template-Rocq syntax to PUIC syntax      |
| [TemplateToPCUICCorrectness] | Type preservation of the aformentioned translation |
| [PCUICToTemplate] | Translation from PCUIC syntax to Template-Rocq syntax |
| [PCUICToTemplateCorrectness] | Type preservation of the aformentioned translation |
| [TemplateToPCUICWcbvEval] | The weak-head call-by-value evaluation strategy is preserved by the translation between Template-Rocq and PCUIC

[TemplateToPCUIC]: ./TemplateToPCUIC.v
[TemplateToPCUICCorrectness]: ./TemplateToPCUICCorrectness.v
[PCUICToTemplate]: ./PCUICToTemplate.v
[PCUICToTemplateCorrectness]: ./PCUICToTemplateCorrectness.v
[TemplateToPCUICWcbvEval]: ./TemplateToPCUICWcbvEval.v
