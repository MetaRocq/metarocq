# MetaRocq

<p align="center">
<img src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/LOGO.png" alt="MetaRocq" width="50px"/>
</p>

[![Build status](https://github.com/MetaRocq/metarocq/actions/workflows/build.yml/badge.svg)](https://github.com/MetaRocq/metarocq/actions) [![MetaRocq Chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://rocq-prover.zulipchat.com)
[![Open in Visual Studio Code](https://img.shields.io/static/v1?logo=visualstudiocode&label=&message=Open%20in%20Visual%20Studio%20Code&labelColor=2c2c32&color=007acc&logoColor=007acc)](https://open.vscode.dev/metarocq/metarocq)

MetaRocq is a project formalizing Rocq in Rocq and providing tools for
manipulating Rocq terms and developing certified plugins
(i.e. translations, compilers or tactics) in Rocq.


**Quick jump**
- [MetaRocq](#metarocq)
  - [Getting started](#getting-started)
  - [Installation instructions](#installation-instructions)
  - [Documentation](#documentation)
  - [Overview of the project](#overview-of-the-project)
    - [Template-Rocq](#template-rocq)
    - [PCUIC](#pcuic)
    - [Safe Checker](#safe-checker)
    - [Erasure](#erasure)
    - [Translations](#translations)
    - [Quotation](#quotation)
    - [Examples](#examples)
  - [Papers](#papers)
  - [Related Projects](#related-projects)
  - [Team \& Credits](#team--credits)
  - [Bugs](#bugs)



## Getting started

- You may want to start with a [demo](https://github.com/MetaRocq/metarocq/blob/-/examples/demo.v).

- The current branch [documentation (as light coqdoc files)](https://metarocq.github.io/html/toc.html).

- The [overview](#overview-of-the-project) of the different parts of the project.



## Installation instructions

See [INSTALL.md](https://github.com/MetaRocq/metarocq/blob/-/INSTALL.md)



## Documentation

See [DOC.md](https://github.com/MetaRocq/metarocq/blob/-/DOC.md)



## Overview of the project

At the center of this project is the Template-Rocq quoting library for
Rocq. The project currently has a single repository extending
Template-Rocq with additional features. Each extension is in a dedicated folder.
The [dependency graph](https://raw.githubusercontent.com/MetaRocq/metarocq/refs/heads/9.0/dependency-graph/depgraph-2022-07-01.svg)
might be useful to navigate the project.
Statistics: ~300kLoC of Rocq, ~30kLoC of OCaml.

### [Template-Rocq](https://github.com/MetaRocq/metarocq/blob/-/template-rocq/theories)

Template-Rocq is a quoting library for [Rocq](http://rocq-prover.org). It
takes `Rocq` terms and constructs a representation of their syntax tree as
an inductive data type. The representation is based on the kernel's
term representation.

After importing `MetaRocq.Template.Loader` there are commands `MetaRocq Test Quote t.`,
`MetaRocq Quote Definition name := (t).` and `MetaRocq Quote Recursively Definition name := (t).` as
well as a tactic `quote_term t k`,
where in all cases `t` is a term and `k` a continuation tactic.

In addition to this representation of terms, Template Rocq includes:

- Reification of the environment structures, for constant and inductive
  declarations along with their universe structures.

- Denotation of terms and global declarations.

- A monad for querying the environment, manipulating global declarations, calling the type
  checker, and inserting them in the global environment, in
  the style of MTac. Monadic programs `p : TemplateMonad A` can be run using `MetaRocq Run p`.

- A formalization of the typing rules reflecting the ones of Rocq, covering all of Rocq
  except eta-expansion and template polymorphism.

### [PCUIC](https://github.com/MetaRocq/metarocq/blob/-/pcuic/theories)

PCUIC, the Polymorphic Cumulative Calculus of Inductive Constructions is
a cleaned up version of the term language of Rocq and its associated
type system, shown equivalent to the one of Rocq. This version of the
calculus has proofs of standard metatheoretical results:

- Weakening for global declarations, weakening and substitution for
  local contexts.

- Confluence of reduction using a notion of parallel reduction

- Context cumulativity / conversion and validity of typing.

- Subject Reduction (case/cofix reduction excluded)

- Principality: every typeable term has a smallest type.

- Bidirectional presentation: an equivalent presentation of the system
  that enforces directionality of the typing rules. Strengthening follows
  from this presentation.

- Elimination restrictions: the elimination restrictions ensure
  that singleton elimination (from Prop to Type) is only allowed
  on singleton inductives in Prop.

- Canonicity: The weak head normal form of a term of inductive type is a constructor application.

- Consistency under the assumption of strong normalization

- Weak call-by-value standardization: Normal forms of terms of first-order inductive type
can be found via weak call-by-value evaluation.

See the PCUIC [README](https://github.com/MetaRocq/metarocq/blob/-/pcuic/theories/README.md) for
a detailed view of the development.

### [Safe Checker](https://github.com/MetaRocq/metarocq/blob/-/safechecker/theories)

Implementation of a fuel-free and verified reduction machine, conversion
checker and type checker for PCUIC. This relies on a postulate of
strong normalization of the reduction relation of PCUIC on well-typed terms.
The checker is shown to be correct and complete w.r.t. the PCUIC specification.
The extracted safe checker is available in Rocq through a new vernacular command:

    MetaRocq SafeCheck <term>

After importing `MetaRocq.SafeChecker.Loader`.

To roughly compare the time used to check a definition with Rocq's vanilla
type-checker, one can use:

    MetaRocq RocqCheck <term>

This also includes a verified, efficient re-typing procedure (useful in tactics) in
`MetaRocq.SafeChecker.PCUICSafeRetyping`.

See the SafeChecker [README](https://github.com/MetaRocq/metarocq/blob/-/safechecker/theories/README.md) for
a detailed view of the development.

### [Erasure](https://github.com/MetaRocq/metarocq/blob/-/erasure/theories)

An erasure procedure to untyped lambda-calculus accomplishing the
same as the type and proof erasure phase of the Extraction plugin of Rocq.
The extracted safe erasure is available in Rocq through a new vernacular command:

    MetaRocq Erase <term>

After importing `MetaRocq.Erasure.Loader`.

The erasure pipeline includes verified optimizations to remove lets in constructors,
remove cases on propositional terms, switch to an unguarded fixpoint reduction rule and
transform the higher-order constructor applications to first-order blocks for easier
translation to usual programming languages. See the erasure
[README](https://github.com/MetaRocq/metarocq/blob/-/erasure/theories/README.md) for
a detailed view of the development.

### [Translations](https://github.com/MetaRocq/metarocq/blob/-/translations)

Examples of translations built on top of this:

- a parametricity plugin in [translations/param_original.v](https://github.com/MetaRocq/metarocq/blob/-/translations/param_original.v)

- a plugin to negate functional extensionality in [translations/times_bool_fun.v](https://github.com/MetaRocq/metarocq/blob/-/translations/times_bool_fun.v)

### [Quotation](https://github.com/MetaRocq/metarocq/blob/-/quotation/theories)

The `Quotation` module is geared at providing functions `□T → □□T` for
`□T := Ast.term` (currently implemented) and for `□T := { t : Ast.term
& Σ ;;; [] |- t : T }` (still in the works).

Ultimately the goal of this development is to prove that `□` is a lax monoidal
semicomonad (a functor with `cojoin : □T → □□T` that codistributes over `unit`
and `×`), which is sufficient for proving Löb's theorem.

The public-facing interface of this development is provided in [`MetaRocq.Quotation.ToTemplate.All`](./quotation/theories/ToTemplate/All.v) and [`MetaRocq.Quotation.ToPCUIC.All`](./quotation/theories/ToPCUIC/All.v).

See the Quotation [README](https://github.com/MetaRocq/metarocq/blob/-/quotation/theories/README.md) for a more detailed view of the development.

### Examples

- An example Rocq plugin built on the Template Monad, which can be used to
  add a constructor to any inductive type is in [examples/add_constructor.v](https://github.com/MetaRocq/metarocq/blob/-/examples/add_constructor.v)

- An example *extracted* Rocq plugin built on the extractable Template Monad, which can be used to
  derive lenses associated to a record type is in [test-suite/plugin-demo](https://github.com/MetaRocq/metarocq/blob/-/test-suite/plugin-demo). The plugin runs in OCaml and is a template for writing extracted plugins.

- An example ``constructor`` tactic written using the Template Monad is in [examples/constructor_tac.v](https://github.com/MetaRocq/metarocq/blob/-/examples/constructor_tac.v),
  and a more elaborate verified tautology checker is in [examples/tauto.v](https://github.com/MetaRocq/metarocq/blob/-/examples/tauto.v).

- The test-suite files [test-suite/erasure_test.v](https://github.com/MetaRocq/metarocq/blob/-/test-suite/erasure_test.v)
  and [test-suite/safechecker_test.v](https://github.com/MetaRocq/metarocq/blob/-/test-suite/safechecker_test.v) show example
  uses (and current limitations of) the extracted verified checker and erasure.

- The [test-suite/self_erasure.v](https://github.com/MetaRocq/metarocq/blob/-/test-suite/self_erasure.v) file checks that erasure
  works on the verified typechecking and erasure programs themselves.

- The test-suite file [test-suite/erasure_live_test.v](https://github.com/MetaRocq/metarocq/blob/-/test-suite/erasure_live_test.v)
  shows uses of the verified erasure running *inside* Rocq.

## Papers

- ["Correct and Complete Type Checking and Certified Erasure for Coq, in Coq"](https://dl.acm.org/doi/10.1145/3706056) Matthieu Sozeau, Yannick Forster, Meven Lennon-Bertrand, Nicolas Tabareau and Théo Winterhalter. Journal of the ACM, Volume 72, Issue 1. January 2025.

  This paper presents the whole metatheoretical development of PCUIC and verified typechecking and erasure, as of version 1.2 of MetaRocq.

- ["Verified Extraction from Coq to OCaml](https://dl.acm.org/doi/10.1145/3656379) Yannick Forster, Matthieu Sozeau and Nicolas Tabareau. PACMPL, Volume 8, Issue PLDI. June 2024. Distinguished Paper Award.

  This presents our [verified extraction](https://github.com/yforster/coq-verified-extraction) pipeline from Coq to OCaml/Malfunction.

- ["The Curious Case of Case"](https://sozeau.gitlabpages.inria.fr/www/research/publications/The_Curious_Case_of_Case-WITS22-220122.pdf) Matthieu Sozeau, Meven Lennon-Bertrand and Yannick Forster. WITS 2022 presentation, Philadelphia.
  This presents the challenges around the representation of cases in Coq and PCUIC.

- ["Bidirectional Typing for the Calculus of Inductive Constructions"](https://www.meven.ac/category/phd-thesis.html) Meven Lennon-Bertrand, PhD thesis, June 2022.
  Part 2 describes in detail the bidirectional variant of typing and its use to verify correctness and completeness of the type checker.

- ["Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq"](https://metarocq.github.io/coqcoqcorrect)
  Matthieu Sozeau, Simon Boulier, Yannick Forster, Nicolas Tabareau
  and Théo Winterhalter. POPL 2020, New Orleans.

  This paper presented the formal proofs of soundness of conversion, type checking and erasure.
  Now superseded by the April 2023 article above.

- ["Formalization and meta-theory of type theory"](https://theowinterhalter.github.io/#phd) Théo Winterhalter, PhD thesis, September 2020.
  Part 3 describes in detail the verified reduction, conversion and type checker.

- ["Coq Coq Codet! Towards a Verified Toolchain for Coq in MetaCoq"](https://sozeau.gitlabpages.inria.fr/www/research/publications/Coq_Coq_Codet-CoqWS19.pdf)
  Matthieu Sozeau, Simon Boulier, Yannick Forster, Nicolas Tabareau and
  Théo Winterhalter. Abstract and
  [presentation](http://www.ps.uni-saarland.de/~forster/downloads/slides-coqws19.pdf)
  given at the [Coq Workshop
  2019](https://staff.aist.go.jp/reynald.affeldt/coq2019/), September
  2019.

- ["The MetaCoq Project"](https://sozeau.gitlabpages.inria.fr/www/research/publications/drafts/The_MetaCoq_Project.pdf)
  Matthieu Sozeau, Abhishek Anand, Simon Boulier, Cyril Cohen, Yannick Forster, Fabian Kunze,
  Gregory Malecha, Nicolas Tabareau and Théo Winterhalter. JAR, February 2020.
  Extended version of the ITP 2018 paper.

  This includes a full documentation of the Template Monad and the typing rules of PCUIC.

- [A certifying extraction with time bounds from Coq to call-by-value λ-calculus](https://www.ps.uni-saarland.de/Publications/documents/ForsterKunze_2019_Certifying-extraction.pdf).
  Yannick Forster and Fabian Kunze.
  ITP 2019.
  [Example](https://github.com/uds-psl/certifying-extraction-with-time-bounds/blob/master/Tactics/Extract.v)

- ["Towards Certified Meta-Programming with Typed Template-Coq"](https://hal.archives-ouvertes.fr/hal-01809681/document)
  Abhishek Anand, Simon Boulier, Cyril Cohen, Matthieu Sozeau and Nicolas Tabareau.
  ITP 2018.

- The system was presented at [Coq'PL 2018](https://popl18.sigplan.org/event/coqpl-2018-typed-template-coq)

## Related Projects

- The [CertiCoq](https://github.com/CertiCoq/certicoq) project develops a certified compiler from the output of verified erasure down
  to CompCert C-light. It provides in particular OCaml and fully foundationally verified plugins
  for the whole compilation pipeline from Gallina to Clight and the verified type-checker of MetaRocq.

- The [ConCert](https://github.com/AU-COBRA/ConCert) project develops certified or certifying compilers from Gallina to smart contract languages (Liquidity and
  CameLIGO), the functional language Elm, and a subset of the Rust programming languages. It uses the typed erasure variant to
  gather more type information about erased terms and perform optimizations based on this information.
  The project focuses in particular on the verification and safe extraction of smart contracts for blockchains.

## Team & Credits

<p align="center">
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/abhishek-anand.jpg"
alt="Abhishek Anand" width="150px"/>
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/danil-annenkov.jpeg"
alt="Danil Annenkov" width="150px"/>
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/simon-boulier.jpg"
alt="Simon Boulier" width="150px"/><br/>
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/cyril-cohen.png"
alt="Cyril Cohen" width="150px"/>
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/yannick-forster.jpg"
alt="Yannick Forster" width="150px"/>
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/jason-gross.jpg" alt="Jason Gross"
width="150px"/><br/>
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/meven-lennon-bertrand.jpeg"
alt="Meven Lennon-Bertrand" width="150px"/>
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/kenji-maillard.jpg"
alt="Kenji Maillard" width="150px"/>
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/gregory-malecha.jpg"
alt="Gregory Malecha" width="150px"/><br/>
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/jakob-botsch-nielsen.png"
alt="Jakob Botsch Nielsen" width="150px"/>
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/matthieu-sozeau.png"
alt="Matthieu Sozeau" width="150px"/>
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/nicolas-tabareau.jpg"
alt="Nicolas Tabareau" width="150px"/><br/>
<img
src="https://github.com/MetaRocq/metarocq.github.io/raw/master/assets/theo-winterhalter.jpg"
alt="Théo Winterhalter" width="150px"/>
<br/>


MetaRocq is developed by (left to right)
<a href="https://github.com/aa755">Abhishek Anand</a>,
<a href="https://github.com/annenkov">Danil Annenkov</a>,
<a href="https://github.com/SimonBoulier">Simon Boulier</a>,
<a href="https://github.com/CohenCyril">Cyril Cohen</a>,
<a href="https://github.com/yforster">Yannick Forster</a>,
<a href="https://jasongross.github.io">Jason Gross</a>,
<a href="https://www.meven.ac">Meven Lennon-Bertrand</a>,
<a href="https://github.com/kyoDralliam">Kenji Maillard</a>,
<a href="https://github.com/gmalecha">Gregory Malecha</a>,
<a href="https://github.com/jakobbotsch">Jakob Botsch Nielsen</a>,
<a href="https://github.com/mattam82">Matthieu Sozeau</a>,
<a href="https://github.com/Tabareau">Nicolas Tabareau</a> and
<a href="https://github.com/TheoWinterhalter">Théo Winterhalter</a>.
</p>


```
Copyright (c) 2014-2023 Gregory Malecha
Copyright (c) 2015-2025 Abhishek Anand, Matthieu Sozeau
Copyright (c) 2017-2023 Simon Boulier, Cyril Cohen
Copyright (c) 2017-2025 Nicolas Tabareau, Yannick Forster, Théo Winterhalter
Copyright (c) 2018-2023 Danil Annenkov
Copyright (c) 2020-2023 Jakob Botsch Nielsen, Meven Lennon-Bertrand
Copyright (c) 2022-2025 Kenji Maillard
Copyright (c) 2023      Jason Gross
```

This software is distributed under the terms of the MIT license.
See [LICENSE](https://github.com/MetaRocq/metarocq/blob/-/LICENSE) for details.

## Bugs

Please report any bugs or feature requests on the github [issue tracker](https://github.com/MetaRocq/metarocq/issues).
