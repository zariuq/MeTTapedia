import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Nodes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Encoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Rules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Instances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Freshness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Represents
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Transfer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Correspondence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Steps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Hosting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Runs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Unification
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.BinderCoreOnTheStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleChoice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Arrows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowHosting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Multiplicity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ScopedText
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Hygiene
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleTwice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleOutOfScope
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleSharedSite
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.NestedCoreHosting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.All
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.All
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.All
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.All
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.All

/-!
# The hosting of the source language's core on the step of a program

A translation of source programs into programs of `RuleSyntax.step` at the contextual frames, and the
correspondence of whole runs, both ways.

* **Alternatives are runs.** A state of the step has one knowledge; an alternative of the source has
  its own store. A state represents one alternative (`Represents`: the alternative's row reads, into
  every frame, exactly as the alternative under the solutions of its store), the step's choice of
  firing is the source's choice of alternative, and a configuration is represented by a frontier of
  the step's runs (`Frontier`), whose answers are the configuration's, as a bag (`frontier_answers`).
  The frontier is one represented state per live alternative: its multiplicities are those of the
  source's live alternatives. Read from the step alone, the **set** of answers is determined
  (`Answers.answers_as_sets`, `Answers.arrow_answers_as_sets`) and the bag is not: two programs with
  different bags have the same rules and the same start state (`Answers.SameStart.bags_differ`).
* **The translation** (`translate`): one schema per equation and six control rules, the same for every
  program; the union of programs goes to the union of the rule sets (`translate_union`). A hosted
  program is its rules and one row per equation, for the negative test of an unmatched call; the
  hosting of a union is the union of the hostings, rules and rows (`Composition.hosted_union`).
* **The first fragment** (`ret`, `apply`, `choice`, `fail`; equations under binders with second-order
  patterns): one firing per source step and every firing a source step (`simulation`, `reflection`);
  whole runs both ways (`runs_forward`, `runs_reflected`), for queries whose names are unopened, a
  hypothesis that is needed (`Controls.Unopened.unopened_needed`); the binder core as a corollary
  (`BinderCoreOnTheStep.binderCore_on_the_step`); at the canonical firing the step's admission is the
  source's unification (`schema_admitted_iff`); existence and controls (`ExampleChoice`).
* **`let`** (`Arrows`, `ArrowSteps`, `ArrowHosting`, `ArrowRuns`): the two `let` moves are one firing
  each, both ways, for hygienic alternatives; hygiene cannot be dropped (`hygiene_needed`) and is not
  necessary (`Controls.HygieneNotNecessary.transfer_holds`); whole runs of the fragment with `let`
  correspond given that every reachable alternative is hygienic (`arrow_runs_forward_of_hygienic`,
  `arrow_runs_reflected_of_hygienic`).
* **Hygiene along every run** (`ScopedText`, `Hygiene`): every alternative that a run of a scoped
  program and query with `let` reaches is hygienic (`reachableHygienic_of_scoped`), by an invariant of
  run-time scoping preserved by every move.
* **The run theorems** (`WellFormedRuns`): `arrow_runs_forward_of_scoped`, `arrow_answers_of_scoped`,
  `arrow_runs_reflected_of_scoped`, with no hypothesis on runs, nested calls included, under the
  clauses their proofs use: every equation scoped, with its own site and its binder sites distinct;
  the query scoped from its site, with distinct sites. The forms for well-formed programs
  (`arrow_runs_forward`, `arrow_answers`, `arrow_runs_reflected`) are corollaries and ask more
  (`Controls.UnusedClauses`). An existence with a call inside a call, written with a `let`
  (`ExampleTwice`); the control outside the scope clause, where the source answers and no run of the
  step answers (`ExampleOutOfScope`); the control outside the distinct-sites clause, where the source
  captures a name and the step does not (`ExampleSharedSite`).
* **The nested-calls core** (`NestedCoreHosting`): the source language's runs of the core's embedding,
  for every program and every ground query, fall under the run theorems (with nodes for its row
  signature). The core's own reduction is not related to those runs here.
* **Multiplicity** (`Multiplicity`): source programs are bags of equations, step programs are sets of
  rules; two equations that differ only in their site have one schema (`translate_duplicate`).
* **What is in each fragment** (`Examples`): which elaborated programs lie in the first fragment
  (`Examples.Fragments`); recursion under a `let`, with two pending frames at two depths
  (`Examples.Recursion`); programs elaborated by value that satisfy the run theorems' hypotheses
  (`Examples.UserPrograms`). Programs whose text has a call through a function variable are not among
  the examples.
* **Composition** (`Composition`): a hosted program beside other rows, knowledge and rules. Its run
  correspondence is unchanged when the knowledge says nothing more of the hosted rows than the
  alternative's store, no other row matches a call that no equation matches (forward direction; not
  asked of programs with no reachable unmatched call), and no other row reads as an alternative's row
  (reflected direction); each condition with its control (`Composition.Neighbours`,
  `Composition.Controls`). Beside other rules, every run of the union is a source run with the other
  rules' firings silent when those firings take no hosted row, add no knowledge of them, and make no row
  that reads as an alternative's row (`Composition.runs_reflected_neighbour`, the reflected direction);
  the forward direction after they have fired holds when also the rows they make never read as
  equation rows (`Composition.AlongRuns.forward_after_neighbour`), and can fail without that clause
  (`Composition.NeighbourControls.switched_off`). The union of two hosted systems
  answers as the union of the programs (`Composition.union_answers`), and as one of them when along its
  runs no equation of the other matches a call (`Composition.union_conservative`).
* **Progress and divergence** (`Divergence`): no alternative of the fragments waits
  (`Divergence.arrow_progress`); the source diverges from a query exactly when the translated program
  diverges from its start (`Divergence.arrow_diverges_iff`, `Divergence.diverges_iff`), a statement
  about the translated program alone: beside other rules that fire for ever the union diverges from
  every start (`Divergence.BesideNeighbours.union_diverges`), and the source diverges exactly when the
  translated program fires infinitely often in a run of the union
  (`Divergence.BesideNeighbours.arrow_diverges_iff_beside`); alternative by alternative the hosting is
  an operational correspondence (`Divergence.alternativesCorrespondence`).
-/
