# Erasure

Implementation of a verified extraction pipeline from PCUIC to untyped lambda calculus
extended with a box construct for erased terms.


| File                    | Description                                          |
|-------------------------|------------------------------------------------------|
| [Prelim]                | Preliminaries on PCUIC
| [EArities]              | Meta-theoretic lemmas on PCUIC needed for erasure correctness
| [EAst]                  | AST of λ-box terms
| [EAstUtils]             | Utility definitions and lemmas on the AST
| [ELiftSubst]            | Lifting and substitution for λ-box terms
| [ECSubst]               | Definition of closed substitution (without lifting)
| [EReflect]              | Reflection of equality on the AST
| [ESpineView]            | Spine-view of λ-box terms (i.e., n-ary applications)
| [EDeps]                 | Definitions of λ-box term dependencies (used to optimize erasure)
| [EEnvMap]               | Efficient global environment definition
| [EGlobalEnv]            | Global environment interface
| [EGenericMapEnv]        | Generic well-formedness preservation proof for global environments
| [EEtaExpanded]          | Eta-expansion predicates on λ-box terms, only for constructors
| [EEtaExpandedFix]       | Eta-expansion predicates on λ-box terms, for constructors and fixpoints
| [EInduction]            | Induction principles on λ-box terms
| [EExtends]              | Weakening of global environments
| [EPretty]               | Pretty-printing of λ-box programs
| [EProgram]              | Definition of well-formed λ-box programs and associated evaluation
| [EWcbvEval]             | Weak call-by-value evaluation definition
| [EWcbvEvalEtaInd]       | Induction principle on weak call-by-value evaluation preserving eta-expansion
| [EWcbvEvalInd]          | Induction principle on weak call-by-value evaluation
| [EWellformed]           | Well-formedness predicate on erased terms
| [Extract]               | The erasure relation
| [ESubstitution]         | Substitution and weakening lemmas for the erasure relation
| [ErasureCorrectness]    | The erasure relation correctness proof 
| [ErasureProperties]     | Properties of the erasure relation
| [ErasureFunction]       | The erasure function defined on well-typed terms and its correctness proof
| [EInlineProjections]    | Transformation that inlines projections to cases
| [EOptimizePropDiscr]    | Transformation removing cases on propositional content
| [EConstructorsAsBlocks] | Transform constructor applications into an atomic construct (always fully-applied constructors)
| [ERemoveParams]         | Remove constructor parameters
| [ETransform]            | Definitions of transformations from PCUIC to λ-box
| [Erasure]               | The complete erasure pipeline
| [Extraction]            | Extraction directives for the plugin
| [Loader]                | Loads the erasure plugin

[EAll]: EAll.v 
[EArities]: EArities.v 
[EAst]: EAst.v 
[EAstUtils]: EAstUtils.v 
[ECSubst]: ECSubst.v 
[ECoFixToFix]: ECoFixToFix.v 
[EDeps]: EDeps.v 
[EEnvMap]: EEnvMap.v 
[EGenericMapEnv]: EGenericMapEnv.v
[EEtaExpanded]: EEtaExpanded.v 
[EEtaExpandedFix]: EEtaExpandedFix.v 
[EExtends]: EExtends.v 
[EGlobalEnv]: EGlobalEnv.v 
[EInduction]: EInduction.v 
[EInlineProjections]: EInlineProjections.v 
[ELiftSubst]: ELiftSubst.v 
[EOptimizePropDiscr]: EOptimizePropDiscr.v 
[EPretty]: EPretty.v 
[EProgram]: EProgram.v 
[EReflect]: EReflect.v 
[ERemoveParams]: ERemoveParams.v 
[ESpineView]: ESpineView.v 
[ESubstitution]: ESubstitution.v 
[ETransform]: ETransform.v 
[EWcbvEval]: EWcbvEval.v 
[EWcbvEvalEtaInd]: EWcbvEvalEtaInd.v 
[EWcbvEvalInd]: EWcbvEvalInd.v 
[EWellformed]: EWellformed.v 
[EWndEval]: EWndEval.v 
[Erasure]: Erasure.v
[EConstructorsAsBlocks]: EConstructorsAsBlocks.v
[ErasureCorrectness]: ErasureCorrectness.v 
[ErasureFunction]: ErasureFunction.v 
[ErasureProperties]: ErasureProperties.v 
[Extract]: Extract.v 
[Extraction]: Extraction.v 
[Loader]: Loader.v 
[Prelim]: Prelim.v