# Quotation

The `Quotation` module is geared at providing functions `□T → □□T` for
`□T := Ast.term` (currently implemented) and for `□T := { t : Ast.term
& Σ ;;; [] |- t : T }` (still in the works).

Ultimately the goal of this development is to prove that `□` is a lax monoidal
semicomonad (a functor with `cojoin : □T → □□T` that codistributes over `unit`
and `×`), which is sufficient for proving Löb's theorem.

The public-facing interface of this development is provided in [`MetaRocq.Quotation.ToTemplate.All`](./ToTemplate/All.v) and [`MetaRocq.Quotation.ToPCUIC.All`](./ToPCUIC/All.v).

## Public-Facing Interface

### Template

In [`MetaRocq.Quotation.ToTemplate.All`](./ToTemplate/All.v):

- `Raw.quote_term : Ast.term -> Ast.term` (the function `cojoin : □T → □□T` for `□T := Ast.term`)

- `Raw.quote_typing {cf : checker_flags} {Σ Γ t T} : (Σ ;;; Γ |- t : T) -> Ast.term`

- `Raw.quote_red {Σ Γ x y} : @red Σ Γ x y -> Ast.term`

- `Raw.quote_wf_local {cf : checker_flags} {Σ Γ} : wf_local Σ Γ -> Ast.term`

- `Raw.quote_wf {cf Σ} : @wf cf Σ -> Ast.term`

- `Raw.quote_wf_ext {cf Σ} : @wf_ext cf Σ -> Ast.term`

- (experimental) `Raw.WfAst.quote_wf {Σ t} : @WfAst.wf Σ t -> Ast.term`


### PCUIC

In [`MetaRocq.Quotation.PCUIC.All`](./ToPCUIC/All.v):

- `Raw.quote_term : PCUICAst.term -> PCUICAst.term` (the function `cojoin : □T → □□T` for `□T := PCUICAst.term`)

- `Raw.quote_typing {cf : checker_flags} {Σ Γ t T} : (Σ ;;; Γ |- t : T) -> PCUICAst.term`

- `Raw.quote_red {Σ Γ x y} : @red Σ Γ x y -> PCUICAst.term`

- `Raw.quote_wf_local {cf : checker_flags} {Σ Γ} : wf_local Σ Γ -> PCUICAst.term`

- `Raw.quote_wf {cf Σ} : @wf cf Σ -> PCUICAst.term`

- `Raw.quote_wf_ext {cf Σ} : @wf_ext cf Σ -> PCUICAst.term`

## Internal File Organization

The rest of the files in this development should be considered as not
part of the public interface.  The organization described here is
subject to change, and is provided for developers and contributors.


Some design principles:

- Quotation is organized around typeclasses for managing automation for finding and constructing functions `T -> Ast.term` for various `T`: `ground_quotable T` for indicating that all ground terms of type `T` can be quoted (by case analysis or induction, generally); `@quotation_of T t` for indicating that the particular term `t : T` has a quotation in `Ast.term`.

- Hints, settings / flags / options, etc are marked `#[export]` and are *not* exported by the `All.v` files, so that such settings remain internal to the development

- Universes associated to types are systematically refreshed / mangled, to avoid universe inconsistencies; universe polymorphism, which is more painful to manage in the TemplateMonad (due in large part to the fact that `tmAxiom` and `tmDefinition` do not support emitting universe-polymorphic constants), is used judiciously.

- To make performance of typeclass resolution managable in the face of hundreds of possible instances for goals of the form `quotation_of _`, typeclass resolution is set up so as to need backtracking as little as possible, and so that constants are opaque to typeclass resolution by default.  On a case-by-case basis, constants are specifically marked transparent (and added to a `quotation` unfold hint database, which is used to unfold constants without associated instances early and all-at-once).

- General quotability of `T` for `T : Prop` or `T := forall a, B` with `B` being subsingleton is proven via decidability: we write a constant `dec : {T} + {~T}`, the obvious function `bdec : {T} + {~T} -> bool`, a proof that `reconstruct : bdec dec = true -> T`, the function `dec_true : T -> bdec dec = true`, and then we can get a function `T -> Ast.term` as `<% reconstruct %>` applied to the quotation of `dec_true t` for some `t : T`, by virtue of the fact that we can quote any equality proof of booleans as either `<% eq_refl true %>` or `<% eq_refl false %>` depending on the booleans.

- In most cases, inductive types are given explicit `ground_quotable` instances, while most defined constants are just made transparent to typeclass inference.  Defined constants containing `match`es or other constructions that make quoting non-trivial are the exception, and are given `ground_quotable` instances as well.  In general, either a constant is made transparent and added to the `quotation` unfolding hint database, *or* it is given a `ground_quotable` instance, (almost) never both.

- Directory and file structure is mirrored between the `Quotation` development and the underlying Rocq development for which quotation theory is being developed.  Sometimes directories are compressed into single files (e.g., [`ToTemplate/Stdlib/Init.v`](./ToTemplate/Stdlib/Init.v) contains quotation theory for everything in the `Stdlib.Init.*` namespace), and other times single files are expanded into a directory (e.g., [`ToTemplate/QuotationOf/Template/Ast/`](./ToTemplate/QuotationOf/Template/Ast/) contains `Foo/Instances.v` for every module `Foo` defined in `MetaRocq.Template.Ast` ([`template-rocq/theories/Ast.v`](https://github.com/MetaRocq/metarocq/tree/coq-8.16/template-rocq/theories/Ast.v))).  Directories are compressed into single files when the quotation theory is quick to typecheck and relatively short; files are expanded into directories when components of the quotation theory take a long time to typecheck, so that file-level parallelism can be better leveraged.

- When possible, we try to minimize the content in `ground_quotable` proofs (in particular, using named induction principles rather than bare fixpoints and avoiding excess conversion, when easy), so that proving that these constructions are well-typed is easier.  (This is still very much a work in progress, and principles making the proving of well-typedness easy are still in the works.)

The important files and directories:

- [`CommonUtils.v`](./CommonUtils.v) - This file defines the utility functions that are shared between Template and PCUIC quotation, including various manipulations of kernames, adjustment of universes for automating quotation, and a utility for getting the body of opaque constants for ease of quotation.

Almost all other strucucture is mirrored between the `ToTemplate/` and `ToPCUIC/` folders, with code being identical whenever possible.


- [`ToTemplate/Init.v`](./ToTemplate/Init.v), [`ToPCUIC/Init.v`](./ToPCUIC/Init.v) - Most of the code is character-for-character identical between these files, differing only in whether the constants refer to `Template.Ast` definitions or `PCUIC.PCUICAst` definitions.  Minor differences are required due to differences in how `term` is structured.  These files define:

  - the typeclasses `quotation_of {T} (t : T) := quoted_term_of : Ast.term` and `ground_quotable T := quote_ground : forall t : T, quotation_of t` which are used for managing quotation in the rest of the development.

  - (The typeclass `inductive_quotation_of` is defined for managing automation of quoting inductives, which have slightly different replacement rules.)

  - Automation `replace_quotation_of` and `make_quotation_of` are defined for solving goals of the form `quotation_of t` when `<% t %>` will contain local variables (`tVar "v"`) or functor-bound constants or inductives (modpaths containing `MPbound` or which share a common prefix with the currently open module in a way that suggests they may reference constants in a currently-open functor): such local variables and transient constants and inductives are replaced via typeclass inference with constants or variables of type `quotation_of v`.  The automation will deliberately error if such a replacement cannot be made.  Setting `Instance: debug_opt := true. Set Printing Implicit.` before running one of these methods will result in a printout of the variables replaced as well as the `quotation_of` goals which could not be solved.

  - Modules `Instances`, `PolymorphicInstances`, and `StrongerInstances` for exposing typeclass instance hints and flags around `quotation_of` and `ground_quotable`.  (Note that no instances nor flag settings are exported by the `All.v` files, allowing for containment of the flag settings and hints used to automate quotation.)

  - `ground_quotable_of_dec`, `ground_quotable_neg_of_dec`, `ground_quotable_neq_of_EqDec` for making use of decidability to quote otherwise-uninspectable terms (`Prop`s and functions)

  - Universe polymorphic `_cps` quotations of projections of some common template-polymorphic inductives, used to avoid universe inconsistencies

  - `ground_quotable_of_iffT`, `ground_quotable_of_iff`, `quote_neg_of_iffT`, `quote_neg_of_iff` for leveraging equivalences to transfer quotations

  - The tactic `unfold_quotation_of` for allowing quotation of `Qed`-opaque terms by routing through Template Monad lookup of the opaque body.

  - Automation `tmDeclareQuotationOfModule` and `tmMakeQuotationOfModule` for declaring and defining `quotation_of` instances for all constants in a module; this is used for managing `Module Type`s and functors containing constants whose quotability needs to be assumed.


- [`ToTemplate/QuotationOf/`](./ToTemplate/QuotationOf/), [`ToPCUIC/QuotationOf/`](./ToPCUIC/QuotationOf/) - These directories develop `quotation_of` instances for various `Module Type`s and functors.  The various `Sig.v` files contain `Module Type`s declaring the instances, while the various `Instances.v` files contain the definitions of `Module`s having these `Module Type`s defining the `quotation_of` instances.  The `Module`s in `Instances.v` files *do not* export `Instance`s, while the `Module Type`s in `Sig.v` files *do*; if the concrete constant needs to be quoted, it can be quoted with `<% ... %>` directly and does not need an instance; when functors take in a `Module Type` argument, by contrast, they do need access to the instances declared.  When `Module`s are nested inside `Module Type`s, the top-level `Module Type` exports all declared instances in the submodules.  Nearly all declarations and definitions in files under `QuotationOf` are fully automated; when well-typedness is eventually proven, that should be fully automated as well for these directories, likely by invoking the Safe Checker.

- Under `ToTemplate/` / `ToPCUIC/`, folders `Stdlib/`, `Equations/`, `Utils/`, `Common/`, and `Template/` or `PCUIC/` develop the `ground_quotable` instances for `Stdlib.*`, `Equations.*`, `MetaRocq.Utils.*`, `MetaRocq.Common.*`, and `MetaRocq.Template.*` or `MetaRocq.PCUIC.*`, respectively.  In `Stdlib/` and `Equations/`, generally one file is given to each folder of the underlying development; in `Utils/`, `Common/`, `Template/`, and `PCUIC/`, files generally correspond one-to-one with the underlying development.

## Debugging Suggestions

Since the quotation development is highly systematically automated, changing definitions in the rest of MetaRocq might break quotation files.
The general pattern is to add quotation instances for anything that is missing.

### `debug_opt`

If some `Instance quote_* : ground_quotable _` starts failing, you can add
```coq
#[local] Instance:debug_opt := true.
```
before the failing `#[export] Instance quote_* ...`.
The printout will look something like
```coq
(Ast.tVar "check"%bs)
(Ast.tVar "check"%bs)
(quotation_of check)
```
Look for `quotation_of` lines, which indicate which that the machinery is having trouble finding an instance for `quotation_of check`.
You can sometimes just add arguments such as `{qcheck : quotation_of check}` to the hypotheses of the failing instance to fix the problem.

### Further Proof Debugging
If the instance proof is not a one-liner, you can look at why the proof is failing in more detail.

For example, if setting `debug_opt` gives an output starting with
```
(Ast.tVar "Hc"%bs)
(Ast.tVar "Hc"%bs)
(quotation_of Hc)
```
We can write
```coq
Set Typeclasses Debug Verbosity 2.
try pose proof (_ : quotation_of Hc).
```
The result might look like
<details><summary>this log</summary>

```
Debug: Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug: Starting resolution with 1 goal(s) under focus and 0 shelved goal(s) in only_classes mode, unbounded
Debug: Launching resolution fixpoint on 1 goals: ?X2211 : (quotation_of Hc)
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2211 status: initial
Debug: considering goal 1 of status initial
Debug: 1: looking for (quotation_of Hc) without backtracking
Debug: 1.1: (*external*) (is_var t; destruct t) on (quotation_of Hc) failed with: pattern-matching failed
Debug: 1.1: (*external*) (progress repeat autounfold with quotation in *) on (quotation_of Hc), 1 subgoal(s)
Debug: Launching resolution fixpoint on 1 goals: ?X2234 : (quotation_of Hc)
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2234 status: initial
Debug: considering goal 1 of status initial
Debug: 1.1-1 : (quotation_of Hc)
Debug: calling eauto recursively at depth 2 on 1 subgoals
Debug: 1.1-1: looking for (quotation_of Hc) without backtracking
Debug: 1.1-1.1: (*external*) (is_var t; destruct t) on (quotation_of Hc) failed with: pattern-matching failed
Debug: 1.1-1.1: (*external*) (progress repeat autounfold with quotation in *) on
(quotation_of Hc) failed with: Failed to progress.
Debug: 1.1-1.1: (*external*) (progress intros) on (quotation_of Hc) failed with: Failed to progress.
Debug: 1.1-1.1: (*external*) (destruct t) on (quotation_of Hc) failed with: pattern-matching failed
Debug: Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug: Starting resolution with 1 goal(s) under focus and 0 shelved goal(s) in only_classes mode, unbounded
Debug: Launching resolution fixpoint on 1 goals: ?X2282 : debug_opt
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2282 status: initial
Debug: considering goal 1 of status initial
Debug: 1: looking for debug_opt without backtracking
Debug: 1.1: exact debug_opt_instance_0 on debug_opt, 0 subgoal(s)
Debug: 1.1: after exact debug_opt_instance_0 finished, 0 goals are shelved and unsolved ( )
Debug: Goal 1 has a success, continuing resolution
Debug:
Calling fixpoint on : 0 initial goals, 0 stuck goals and 0 non-stuck failures kept with progress made in this run.
Stuck:
Failed:
Initial:
Debug: Result goals after fixpoint: 0 goals:
Debug: after eauto_tac_stuck: 0 goals:
Debug: The tactic trace is: simple refine debug_opt_instance_0;shelve_goals
Debug: Finished resolution with a complete solution.
Old typeclass evars not concerned by this resolution =
Shelf =
Debug: New typeclass evars are:
Debug: 1.1-1.1: (*external*) (replace_quotation_of_goal ltac:(())) on
(quotation_of Hc) failed with: In nested Ltac calls to "replace_quotation_of_goal" and
                               "run_template_program (constr) (tactic)", last call failed.
                               Avoiding loops
Debug: 1.1-1.1: simple apply @quote_ground on (quotation_of Hc), 1 subgoal(s)
Debug: Launching resolution fixpoint on 1 goals:
?X2283 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2283 status: initial
Debug: considering goal 1 of status initial
Debug: 1.1-1.1-1 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug: calling eauto recursively at depth 3 on 1 subgoals
Debug: 1.1-1.1-1: looking for (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) without backtracking
Debug: 1.1-1.1-1.1: simple apply quote_cproperty on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Cannot unify
(MROption.option_default (fun tm : term => checking Σ tm (j_typ (TermTyp b t))) (j_term (TermTyp b t)) unit) and
(checking Σ b (j_typ (TermTyp b t)))
Debug: 1.1-1.1-1.1: (*external*) (is_var t; destruct t) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: pattern-matching failed
Debug: 1.1-1.1-1.1: (*external*) (progress repeat autounfold with quotation in *) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Failed to progress.
Debug: 1.1-1.1-1.1: (*external*) (progress intros) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Failed to progress.
Debug: 1.1-1.1-1.1: (*external*) (destruct t) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: pattern-matching failed
Debug: 1.1-1.1-1: no match for (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))), 5 possibilities
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.1-1.1: simple apply @quote_ground failed with: Proof-search failed.
Debug:
1.1-1.2: simple apply @BasicAst.quotation_of_mfixpoint failed with: Cannot unify (quotation_of ?M20949) and
(quotation_of Hc)
Debug: Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug: Starting resolution with 1 goal(s) under focus and 0 shelved goal(s) in only_classes mode, unbounded
Debug: Launching resolution fixpoint on 1 goals: ?X2308 : debug_opt
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2308 status: initial
Debug: considering goal 1 of status initial
Debug: 1: looking for debug_opt without backtracking
Debug: 1.1: exact debug_opt_instance_0 on debug_opt, 0 subgoal(s)
Debug: 1.1: after exact debug_opt_instance_0 finished, 0 goals are shelved and unsolved ( )
Debug: Goal 1 has a success, continuing resolution
Debug:
Calling fixpoint on : 0 initial goals, 0 stuck goals and 0 non-stuck failures kept with progress made in this run.
Stuck:
Failed:
Initial:
Debug: Result goals after fixpoint: 0 goals:
Debug: after eauto_tac_stuck: 0 goals:
Debug: The tactic trace is: simple refine debug_opt_instance_0;shelve_goals
Debug: Finished resolution with a complete solution.
Old typeclass evars not concerned by this resolution =
Shelf =
Debug: New typeclass evars are:
(Ast.tVar "Hc"%bs)
Debug:
1.1-1.2: (*external*) (make_quotation_of_goal ltac:(())) failed with: In nested Ltac calls to
                                                                      "make_quotation_of_goal" and
                                                                      "run_template_program (constr) (tactic)", last call
                                                                      failed.
                                                                      bound argument is not ground
Debug: 1.1-1.2: simple apply @qquotation on (quotation_of Hc), 1 subgoal(s)
Debug: Launching resolution fixpoint on 1 goals: ?X2309 : (inductive_quotation_of Hc)
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2309 status: initial
Debug: considering goal 1 of status initial
Debug: 1.1-1.2-1 : (inductive_quotation_of Hc)
Debug: calling eauto recursively at depth 3 on 1 subgoals
Debug: 1.1-1.2-1: looking for (inductive_quotation_of Hc) without backtracking
Debug: 1.1-1.2-1.1: (*external*) (progress intros) on (inductive_quotation_of Hc) failed with: Failed to progress.
Debug: 1.1-1.2-1.1: (*external*) simple notypeclasses refine (default_inductive_quotation_of _ _) on
(inductive_quotation_of Hc), 2 subgoal(s)
Debug: Launching resolution fixpoint on 2 goals:
?X2311 : (quotation_of Hc)
?X2313 : (cls_is_true match ?qt with
                      | Ast.tInd _ _ => true
                      | _ => false
                      end)
Debug:
Calling fixpoint on : 2 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2311 status: initial
Goal 2 evar: ?X2313 status: initial
Debug: considering goal 1 of status initial
Debug: 1.1-1.2-1.1-1 : (quotation_of Hc)
Debug: calling eauto recursively at depth 4 on 1 subgoals
Debug: 1.1-1.2-1.1-1: looking for (quotation_of Hc) with backtracking
Debug: 1.1-1.2-1.1-1.1: (*external*) (is_var t; destruct t) on (quotation_of Hc) failed with: pattern-matching failed
Debug: 1.1-1.2-1.1-1.1: (*external*) (progress repeat autounfold with quotation in *) on
(quotation_of Hc) failed with: Failed to progress.
Debug: 1.1-1.2-1.1-1.1: (*external*) (progress intros) on (quotation_of Hc) failed with: Failed to progress.
Debug: 1.1-1.2-1.1-1.1: (*external*) (destruct t) on (quotation_of Hc) failed with: pattern-matching failed
Debug: Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug: Starting resolution with 1 goal(s) under focus and 0 shelved goal(s) in only_classes mode, unbounded
Debug: Launching resolution fixpoint on 1 goals: ?X2338 : debug_opt
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2338 status: initial
Debug: considering goal 1 of status initial
Debug: 1: looking for debug_opt without backtracking
Debug: 1.1: exact debug_opt_instance_0 on debug_opt, 0 subgoal(s)
Debug: 1.1: after exact debug_opt_instance_0 finished, 0 goals are shelved and unsolved ( )
Debug: Goal 1 has a success, continuing resolution
Debug:
Calling fixpoint on : 0 initial goals, 0 stuck goals and 0 non-stuck failures kept with progress made in this run.
Stuck:
Failed:
Initial:
Debug: Result goals after fixpoint: 0 goals:
Debug: after eauto_tac_stuck: 0 goals:
Debug: The tactic trace is: simple refine debug_opt_instance_0;shelve_goals
Debug: Finished resolution with a complete solution.
Old typeclass evars not concerned by this resolution =
Shelf =
Debug: New typeclass evars are:
Debug: 1.1-1.2-1.1-1.1: (*external*) (replace_quotation_of_goal ltac:(())) on
(quotation_of Hc) failed with: In nested Ltac calls to "replace_quotation_of_goal" and
                               "run_template_program (constr) (tactic)", last call failed.
                               Avoiding loops
Debug: 1.1-1.2-1.1-1.1: simple apply @quote_ground on (quotation_of Hc), 1 subgoal(s)
Debug: Launching resolution fixpoint on 1 goals:
?X2339 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2339 status: initial
Debug: considering goal 1 of status initial
Debug: 1.1-1.2-1.1-1.1-1 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug: calling eauto recursively at depth 5 on 1 subgoals
Debug:
1.1-1.2-1.1-1.1-1: looking for (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) with backtracking
Debug: 1.1-1.2-1.1-1.1-1.1: simple apply quote_cproperty on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Cannot unify
(MROption.option_default (fun tm : term => checking Σ tm (j_typ (TermTyp b t))) (j_term (TermTyp b t)) unit) and
(checking Σ b (j_typ (TermTyp b t)))
Debug: 1.1-1.2-1.1-1.1-1.1: (*external*) (is_var t; destruct t) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: pattern-matching failed
Debug: 1.1-1.2-1.1-1.1-1.1: (*external*) (progress repeat autounfold with quotation in *) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Failed to progress.
Debug: 1.1-1.2-1.1-1.1-1.1: (*external*) (progress intros) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Failed to progress.
Debug: 1.1-1.2-1.1-1.1-1.1: (*external*) (destruct t) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: pattern-matching failed
Debug:
1.1-1.2-1.1-1.1-1: no match for (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))), 5 possibilities
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.1-1.2-1.1-1.1: simple apply @quote_ground failed with: Proof-search failed.
Debug:
1.1-1.2-1.1-1.2: simple apply @BasicAst.quotation_of_mfixpoint failed with: Cannot unify (quotation_of ?M20949) and
(quotation_of Hc)
Debug: Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug: Starting resolution with 1 goal(s) under focus and 0 shelved goal(s) in only_classes mode, unbounded
Debug: Launching resolution fixpoint on 1 goals: ?X2364 : debug_opt
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2364 status: initial
Debug: considering goal 1 of status initial
Debug: 1: looking for debug_opt without backtracking
Debug: 1.1: exact debug_opt_instance_0 on debug_opt, 0 subgoal(s)
Debug: 1.1: after exact debug_opt_instance_0 finished, 0 goals are shelved and unsolved ( )
Debug: Goal 1 has a success, continuing resolution
Debug:
Calling fixpoint on : 0 initial goals, 0 stuck goals and 0 non-stuck failures kept with progress made in this run.
Stuck:
Failed:
Initial:
Debug: Result goals after fixpoint: 0 goals:
Debug: after eauto_tac_stuck: 0 goals:
Debug: The tactic trace is: simple refine debug_opt_instance_0;shelve_goals
Debug: Finished resolution with a complete solution.
Old typeclass evars not concerned by this resolution =
Shelf =
Debug: New typeclass evars are:
(Ast.tVar "Hc"%bs)
Debug:
1.1-1.2-1.1-1.2: (*external*) (make_quotation_of_goal ltac:(())) failed with: In nested Ltac calls to
                                                                              "make_quotation_of_goal" and
                                                                              "run_template_program (constr) (tactic)",
                                                                              last call failed.
                                                                              bound argument is not ground
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.1-1.2-1.1: (*external*) simple notypeclasses refine
(default_inductive_quotation_of _ _) failed with: Proof-search failed.
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.1-1.2: simple apply @qquotation failed with: Proof-search failed.
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.1: (*external*) (progress repeat autounfold with quotation in *) failed with: Proof-search failed.
Debug: 1.2: (*external*) (progress intros) failed with: Failed to progress.
Debug: 1.2: (*external*) (destruct t) failed with: pattern-matching failed
Debug: Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug: Starting resolution with 1 goal(s) under focus and 0 shelved goal(s) in only_classes mode, unbounded
Debug: Launching resolution fixpoint on 1 goals: ?X2366 : debug_opt
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2366 status: initial
Debug: considering goal 1 of status initial
Debug: 1: looking for debug_opt without backtracking
Debug: 1.1: exact debug_opt_instance_0 on debug_opt, 0 subgoal(s)
Debug: 1.1: after exact debug_opt_instance_0 finished, 0 goals are shelved and unsolved ( )
Debug: Goal 1 has a success, continuing resolution
Debug:
Calling fixpoint on : 0 initial goals, 0 stuck goals and 0 non-stuck failures kept with progress made in this run.
Stuck:
Failed:
Initial:
Debug: Result goals after fixpoint: 0 goals:
Debug: after eauto_tac_stuck: 0 goals:
Debug: The tactic trace is: simple refine debug_opt_instance_0;shelve_goals
Debug: Finished resolution with a complete solution.
Old typeclass evars not concerned by this resolution =
Shelf =
Debug: New typeclass evars are:
Debug:
1.2: (*external*) (replace_quotation_of_goal ltac:(())) failed with: In nested Ltac calls to "replace_quotation_of_goal" and
                                                                     "run_template_program (constr) (tactic)", last call
                                                                     failed.
                                                                     Avoiding loops
Debug: 1.2: simple apply @quote_ground on (quotation_of Hc), 1 subgoal(s)
Debug: Launching resolution fixpoint on 1 goals:
?X2367 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2367 status: initial
Debug: considering goal 1 of status initial
Debug: 1.2-1 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug: calling eauto recursively at depth 2 on 1 subgoals
Debug: 1.2-1: looking for (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) without backtracking
Debug: 1.2-1.1: simple apply quote_cproperty on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Cannot unify
(MROption.option_default (fun tm : term => checking Σ tm (j_typ (TermTyp b t))) (j_term (TermTyp b t)) unit) and
(checking Σ b (j_typ (TermTyp b t)))
Debug: 1.2-1.1: (*external*) (is_var t; destruct t) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: pattern-matching failed
Debug: 1.2-1.1: (*external*) (progress repeat autounfold with quotation in *) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))), 1 subgoal(s)
Debug: Launching resolution fixpoint on 1 goals:
?X2390 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2390 status: initial
Debug: considering goal 1 of status initial
Debug: 1.2-1.1-1 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug: calling eauto recursively at depth 3 on 1 subgoals
Debug: 1.2-1.1-1: looking for (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) without backtracking
Debug: 1.2-1.1-1.1: simple apply quote_cproperty on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Cannot unify
(MROption.option_default (fun tm : term => checking Σ tm (j_typ (TermTyp b t))) (j_term (TermTyp b t)) unit) and
(checking Σ b (j_typ (TermTyp b t)))
Debug: 1.2-1.1-1.1: (*external*) (is_var t; destruct t) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: pattern-matching failed
Debug: 1.2-1.1-1.1: (*external*) (progress repeat autounfold with quotation in *) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Failed to progress.
Debug: 1.2-1.1-1.1: (*external*) (progress intros) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Failed to progress.
Debug: 1.2-1.1-1.1: (*external*) (destruct t) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: pattern-matching failed
Debug: 1.2-1.1-1: no match for (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))), 5 possibilities
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.2-1.1: (*external*) (progress repeat autounfold with quotation in *) failed with: Proof-search failed.
Debug: 1.2-1.2: (*external*) (progress intros) failed with: Failed to progress.
Debug: 1.2-1.2: (*external*) (destruct t) failed with: pattern-matching failed
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.2: simple apply @quote_ground failed with: Proof-search failed.
Debug:
1.3: simple apply @BasicAst.quotation_of_mfixpoint failed with: Cannot unify (quotation_of ?M20949) and
(quotation_of Hc)
Debug: Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug: Starting resolution with 1 goal(s) under focus and 0 shelved goal(s) in only_classes mode, unbounded
Debug: Launching resolution fixpoint on 1 goals: ?X2438 : debug_opt
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2438 status: initial
Debug: considering goal 1 of status initial
Debug: 1: looking for debug_opt without backtracking
Debug: 1.1: exact debug_opt_instance_0 on debug_opt, 0 subgoal(s)
Debug: 1.1: after exact debug_opt_instance_0 finished, 0 goals are shelved and unsolved ( )
Debug: Goal 1 has a success, continuing resolution
Debug:
Calling fixpoint on : 0 initial goals, 0 stuck goals and 0 non-stuck failures kept with progress made in this run.
Stuck:
Failed:
Initial:
Debug: Result goals after fixpoint: 0 goals:
Debug: after eauto_tac_stuck: 0 goals:
Debug: The tactic trace is: simple refine debug_opt_instance_0;shelve_goals
Debug: Finished resolution with a complete solution.
Old typeclass evars not concerned by this resolution =
Shelf =
Debug: New typeclass evars are:
(Ast.tVar "Hc"%bs)
Debug:
1.3: (*external*) (make_quotation_of_goal ltac:(())) failed with: In nested Ltac calls to "make_quotation_of_goal" and
                                                                  "run_template_program (constr) (tactic)", last call
                                                                  failed.
                                                                  bound argument is not ground
Debug: 1.3: simple apply @qquotation on (quotation_of Hc), 1 subgoal(s)
Debug: Launching resolution fixpoint on 1 goals: ?X2439 : (inductive_quotation_of Hc)
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2439 status: initial
Debug: considering goal 1 of status initial
Debug: 1.3-1 : (inductive_quotation_of Hc)
Debug: calling eauto recursively at depth 2 on 1 subgoals
Debug: 1.3-1: looking for (inductive_quotation_of Hc) without backtracking
Debug: 1.3-1.1: (*external*) (progress intros) on (inductive_quotation_of Hc) failed with: Failed to progress.
Debug: 1.3-1.1: (*external*) simple notypeclasses refine (default_inductive_quotation_of _ _) on
(inductive_quotation_of Hc), 2 subgoal(s)
Debug: Launching resolution fixpoint on 2 goals:
?X2441 : (quotation_of Hc)
?X2443 : (cls_is_true match ?qt with
                      | Ast.tInd _ _ => true
                      | _ => false
                      end)
Debug:
Calling fixpoint on : 2 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2441 status: initial
Goal 2 evar: ?X2443 status: initial
Debug: considering goal 1 of status initial
Debug: 1.3-1.1-1 : (quotation_of Hc)
Debug: calling eauto recursively at depth 3 on 1 subgoals
Debug: 1.3-1.1-1: looking for (quotation_of Hc) with backtracking
Debug: 1.3-1.1-1.1: (*external*) (is_var t; destruct t) on (quotation_of Hc) failed with: pattern-matching failed
Debug: 1.3-1.1-1.1: (*external*) (progress repeat autounfold with quotation in *) on (quotation_of Hc), 1 subgoal(s)
Debug: Launching resolution fixpoint on 1 goals: ?X2466 : (quotation_of Hc)
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2466 status: initial
Debug: considering goal 1 of status initial
Debug: 1.3-1.1-1.1-1 : (quotation_of Hc)
Debug: calling eauto recursively at depth 4 on 1 subgoals
Debug: 1.3-1.1-1.1-1: looking for (quotation_of Hc) with backtracking
Debug: 1.3-1.1-1.1-1.1: (*external*) (is_var t; destruct t) on (quotation_of Hc) failed with: pattern-matching failed
Debug: 1.3-1.1-1.1-1.1: (*external*) (progress repeat autounfold with quotation in *) on
(quotation_of Hc) failed with: Failed to progress.
Debug: 1.3-1.1-1.1-1.1: (*external*) (progress intros) on (quotation_of Hc) failed with: Failed to progress.
Debug: 1.3-1.1-1.1-1.1: (*external*) (destruct t) on (quotation_of Hc) failed with: pattern-matching failed
Debug: Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug: Starting resolution with 1 goal(s) under focus and 0 shelved goal(s) in only_classes mode, unbounded
Debug: Launching resolution fixpoint on 1 goals: ?X2514 : debug_opt
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2514 status: initial
Debug: considering goal 1 of status initial
Debug: 1: looking for debug_opt without backtracking
Debug: 1.1: exact debug_opt_instance_0 on debug_opt, 0 subgoal(s)
Debug: 1.1: after exact debug_opt_instance_0 finished, 0 goals are shelved and unsolved ( )
Debug: Goal 1 has a success, continuing resolution
Debug:
Calling fixpoint on : 0 initial goals, 0 stuck goals and 0 non-stuck failures kept with progress made in this run.
Stuck:
Failed:
Initial:
Debug: Result goals after fixpoint: 0 goals:
Debug: after eauto_tac_stuck: 0 goals:
Debug: The tactic trace is: simple refine debug_opt_instance_0;shelve_goals
Debug: Finished resolution with a complete solution.
Old typeclass evars not concerned by this resolution =
Shelf =
Debug: New typeclass evars are:
Debug: 1.3-1.1-1.1-1.1: (*external*) (replace_quotation_of_goal ltac:(())) on
(quotation_of Hc) failed with: In nested Ltac calls to "replace_quotation_of_goal" and
                               "run_template_program (constr) (tactic)", last call failed.
                               Avoiding loops
Debug: 1.3-1.1-1.1-1.1: simple apply @quote_ground on (quotation_of Hc), 1 subgoal(s)
Debug: Launching resolution fixpoint on 1 goals:
?X2515 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2515 status: initial
Debug: considering goal 1 of status initial
Debug: 1.3-1.1-1.1-1.1-1 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug: calling eauto recursively at depth 5 on 1 subgoals
Debug:
1.3-1.1-1.1-1.1-1: looking for (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) with backtracking
Debug: 1.3-1.1-1.1-1.1-1.1: simple apply quote_cproperty on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Cannot unify
(MROption.option_default (fun tm : term => checking Σ tm (j_typ (TermTyp b t))) (j_term (TermTyp b t)) unit) and
(checking Σ b (j_typ (TermTyp b t)))
Debug: 1.3-1.1-1.1-1.1-1.1: (*external*) (is_var t; destruct t) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: pattern-matching failed
Debug: 1.3-1.1-1.1-1.1-1.1: (*external*) (progress repeat autounfold with quotation in *) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Failed to progress.
Debug: 1.3-1.1-1.1-1.1-1.1: (*external*) (progress intros) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Failed to progress.
Debug: 1.3-1.1-1.1-1.1-1.1: (*external*) (destruct t) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: pattern-matching failed
Debug:
1.3-1.1-1.1-1.1-1: no match for (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))), 5 possibilities
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.3-1.1-1.1-1.1: simple apply @quote_ground failed with: Proof-search failed.
Debug:
1.3-1.1-1.1-1.2: simple apply @BasicAst.quotation_of_mfixpoint failed with: Cannot unify (quotation_of ?M20949) and
(quotation_of Hc)
Debug: Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug: Starting resolution with 1 goal(s) under focus and 0 shelved goal(s) in only_classes mode, unbounded
Debug: Launching resolution fixpoint on 1 goals: ?X2540 : debug_opt
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2540 status: initial
Debug: considering goal 1 of status initial
Debug: 1: looking for debug_opt without backtracking
Debug: 1.1: exact debug_opt_instance_0 on debug_opt, 0 subgoal(s)
Debug: 1.1: after exact debug_opt_instance_0 finished, 0 goals are shelved and unsolved ( )
Debug: Goal 1 has a success, continuing resolution
Debug:
Calling fixpoint on : 0 initial goals, 0 stuck goals and 0 non-stuck failures kept with progress made in this run.
Stuck:
Failed:
Initial:
Debug: Result goals after fixpoint: 0 goals:
Debug: after eauto_tac_stuck: 0 goals:
Debug: The tactic trace is: simple refine debug_opt_instance_0;shelve_goals
Debug: Finished resolution with a complete solution.
Old typeclass evars not concerned by this resolution =
Shelf =
Debug: New typeclass evars are:
(Ast.tVar "Hc"%bs)
Debug:
1.3-1.1-1.1-1.2: (*external*) (make_quotation_of_goal ltac:(())) failed with: In nested Ltac calls to
                                                                              "make_quotation_of_goal" and
                                                                              "run_template_program (constr) (tactic)",
                                                                              last call failed.
                                                                              bound argument is not ground
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.3-1.1-1.1: (*external*) (progress repeat autounfold with quotation in *) failed with: Proof-search failed.
Debug: 1.3-1.1-1.2: (*external*) (progress intros) failed with: Failed to progress.
Debug: 1.3-1.1-1.2: (*external*) (destruct t) failed with: pattern-matching failed
Debug: Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug: Starting resolution with 1 goal(s) under focus and 0 shelved goal(s) in only_classes mode, unbounded
Debug: Launching resolution fixpoint on 1 goals: ?X2542 : debug_opt
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2542 status: initial
Debug: considering goal 1 of status initial
Debug: 1: looking for debug_opt without backtracking
Debug: 1.1: exact debug_opt_instance_0 on debug_opt, 0 subgoal(s)
Debug: 1.1: after exact debug_opt_instance_0 finished, 0 goals are shelved and unsolved ( )
Debug: Goal 1 has a success, continuing resolution
Debug:
Calling fixpoint on : 0 initial goals, 0 stuck goals and 0 non-stuck failures kept with progress made in this run.
Stuck:
Failed:
Initial:
Debug: Result goals after fixpoint: 0 goals:
Debug: after eauto_tac_stuck: 0 goals:
Debug: The tactic trace is: simple refine debug_opt_instance_0;shelve_goals
Debug: Finished resolution with a complete solution.
Old typeclass evars not concerned by this resolution =
Shelf =
Debug: New typeclass evars are:
Debug:
1.3-1.1-1.2: (*external*) (replace_quotation_of_goal ltac:(())) failed with: In nested Ltac calls to
                                                                             "replace_quotation_of_goal" and
                                                                             "run_template_program (constr) (tactic)",
                                                                             last call failed.
                                                                             Avoiding loops
Debug: 1.3-1.1-1.2: simple apply @quote_ground on (quotation_of Hc), 1 subgoal(s)
Debug: Launching resolution fixpoint on 1 goals:
?X2543 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2543 status: initial
Debug: considering goal 1 of status initial
Debug: 1.3-1.1-1.2-1 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug: calling eauto recursively at depth 4 on 1 subgoals
Debug: 1.3-1.1-1.2-1: looking for (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) with backtracking
Debug: 1.3-1.1-1.2-1.1: simple apply quote_cproperty on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Cannot unify
(MROption.option_default (fun tm : term => checking Σ tm (j_typ (TermTyp b t))) (j_term (TermTyp b t)) unit) and
(checking Σ b (j_typ (TermTyp b t)))
Debug: 1.3-1.1-1.2-1.1: (*external*) (is_var t; destruct t) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: pattern-matching failed
Debug: 1.3-1.1-1.2-1.1: (*external*) (progress repeat autounfold with quotation in *) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))), 1 subgoal(s)
Debug: Launching resolution fixpoint on 1 goals:
?X2566 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2566 status: initial
Debug: considering goal 1 of status initial
Debug: 1.3-1.1-1.2-1.1-1 : (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu)))
Debug: calling eauto recursively at depth 5 on 1 subgoals
Debug:
1.3-1.1-1.2-1.1-1: looking for (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) with backtracking
Debug: 1.3-1.1-1.2-1.1-1.1: simple apply quote_cproperty on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Cannot unify
(MROption.option_default (fun tm : term => checking Σ tm (j_typ (TermTyp b t))) (j_term (TermTyp b t)) unit) and
(checking Σ b (j_typ (TermTyp b t)))
Debug: 1.3-1.1-1.2-1.1-1.1: (*external*) (is_var t; destruct t) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: pattern-matching failed
Debug: 1.3-1.1-1.2-1.1-1.1: (*external*) (progress repeat autounfold with quotation in *) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Failed to progress.
Debug: 1.3-1.1-1.2-1.1-1.1: (*external*) (progress intros) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Failed to progress.
Debug: 1.3-1.1-1.2-1.1-1.1: (*external*) (destruct t) on
(ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))) failed with: pattern-matching failed
Debug:
1.3-1.1-1.2-1.1-1: no match for (ground_quotable (cproperty Σ all b (j_typ (TermTyp b t)) (fst tu))), 5 possibilities
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.3-1.1-1.2-1.1: (*external*) (progress repeat autounfold with quotation in *) failed with: Proof-search failed.
Debug: 1.3-1.1-1.2-1.2: (*external*) (progress intros) failed with: Failed to progress.
Debug: 1.3-1.1-1.2-1.2: (*external*) (destruct t) failed with: pattern-matching failed
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.3-1.1-1.2: simple apply @quote_ground failed with: Proof-search failed.
Debug:
1.3-1.1-1.3: simple apply @BasicAst.quotation_of_mfixpoint failed with: Cannot unify (quotation_of ?M20949) and
(quotation_of Hc)
Debug: Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug: Starting resolution with 1 goal(s) under focus and 0 shelved goal(s) in only_classes mode, unbounded
Debug: Launching resolution fixpoint on 1 goals: ?X2614 : debug_opt
Debug:
Calling fixpoint on : 1 initial goals, 0 stuck goals and 0 non-stuck failures kept with no progress made in this run.
Stuck:
Failed:
Initial: Goal 1 evar: ?X2614 status: initial
Debug: considering goal 1 of status initial
Debug: 1: looking for debug_opt without backtracking
Debug: 1.1: exact debug_opt_instance_0 on debug_opt, 0 subgoal(s)
Debug: 1.1: after exact debug_opt_instance_0 finished, 0 goals are shelved and unsolved ( )
Debug: Goal 1 has a success, continuing resolution
Debug:
Calling fixpoint on : 0 initial goals, 0 stuck goals and 0 non-stuck failures kept with progress made in this run.
Stuck:
Failed:
Initial:
Debug: Result goals after fixpoint: 0 goals:
Debug: after eauto_tac_stuck: 0 goals:
Debug: The tactic trace is: simple refine debug_opt_instance_0;shelve_goals
Debug: Finished resolution with a complete solution.
Old typeclass evars not concerned by this resolution =
Shelf =
Debug: New typeclass evars are:
(Ast.tVar "Hc"%bs)
Debug:
1.3-1.1-1.3: (*external*) (make_quotation_of_goal ltac:(())) failed with: In nested Ltac calls to
                                                                          "make_quotation_of_goal" and
                                                                          "run_template_program (constr) (tactic)", last
                                                                          call failed.
                                                                          bound argument is not ground
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.3-1.1: (*external*) simple notypeclasses refine
(default_inductive_quotation_of _ _) failed with: Proof-search failed.
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
Debug: 1.3: simple apply @qquotation failed with: Proof-search failed.
Debug: Goal 1 has no more solutions, returning exception: NoApplicableHint
```
</details>

The important lines are
```
Debug: 1.1-1.1-1: looking for (ground_quotable (cproperty Γ all b (j_typ (TermTyp b t)) (fst tu))) without backtracking
Debug: 1.1-1.1-1.1: simple apply quote_cproperty on
(ground_quotable (cproperty Γ all b (j_typ (TermTyp b t)) (fst tu))) failed with: Cannot unify
(MROption.option_default (fun tm : term => checking Γ tm (j_typ (TermTyp b t))) (j_term (TermTyp b t)) unit) and
(checking Γ b (j_typ (TermTyp b t)))
```
The problem is that, for performance, we have told typeclass resolution to not unfold any constants, and so we fail to reduce `MROption.option_default` and `j_term`.
Adding something like `cbn [MROption.option_default j_term] in *` to manually unfold these constants can resolve the issue.

Note that if it is not clear what's going wrong, you can also
```coq
Set Debug "tactic-unification".
```
This setting will add, between the above lines, a unification trace ending in
```
Debug:
[tactic-unification] Starting unification: MROption.option_default (fun tm : term => checking Γ tm (j_typ (TermTyp b t)))
                                             (j_term (TermTyp b t)) unit ~= checking Γ b (j_typ (TermTyp b t))
Debug: [tactic-unification] Leaving unification with failure
```
