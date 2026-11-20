import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Syntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.WellFormed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Elaboration
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.BinderCore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.BinderCoreAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NestedCore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Laws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.LawExtension
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExamplesWellFormed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleBeta
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleLet
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleSpaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHeld
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHeldRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleAnnotated
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleTransfer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleExtension
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleExtensionApplied
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleConstructs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleStuckCall
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.LawDeclarations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.LawRenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleRenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleByValue
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleByName
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleRunsAgain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Hygiene
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ElaborationHygiene
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleCapture
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleCaptureRepaired
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Observation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleWaiting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ObservationRenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Outcomes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.AnswerCollection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Worlds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleRace
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleScopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHandles
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleNew

/-!
# A higher-order source language with explicit holding and running

* `Syntax`: data (binding terms of a signature, names keyed by binder sites), the explicit core
  (`ret`, `apply`, `run`, `let_`, `choice`, `fail`, `query`, `add`, `remove`, `new`, `check`,
  `delay`, `force`), equations, programs, configurations.
* `Semantics`: stores of equations per alternative, the moves, the steps on a bag of alternatives,
  the answers as a bag of reading sets.
* `WellFormed`: the pattern class, lexical scope by sites, distinct sites; each decided. It is a
  syntactic check: it does not ensure principal stores (`ExampleWaiting`).
* `Elaboration`: MeTTa text with marks, declarations, the type discipline, the parameters (strategy
  by position, the two reading bits), the elaboration that inserts holding and running, and the
  reading of text as code at run time, with its arrows at sites fresh for the text it reads.
* **Text read as code without capture**: `Hygiene` (uniform binders along every run, under a
  hygienic reading; two most general solutions give mutual instances), `ElaborationHygiene` (the
  elaboration's reading is hygienic), `ExampleCapture` (the control: a reading at fixed sites
  captures), `ExampleCaptureRepaired` (the same program and choices under the elaboration's reading:
  no capture, the two choices agree).
* **What a configuration shows**: `Observation` (answers, refusals, and waiting with its reason, a
  typed none query; exactly three ways to wait), `ExampleWaiting` (failing and waiting told apart; a
  well-formed program whose `run` waits), `ObservationRenaming` (the renaming law for observations).
* **Alternatives and shared spaces**: `Outcomes` (the set of bags of a program; races; moves that
  leave the world as it is commute), `Worlds` (the design not taken: alternatives as worlds, the
  merge and its laws, the shared semantics as its instance on runs that write nothing),
  `ExampleRace` (the race, both semantics on the measured programs), `ExampleScopes` (moves that take
  fresh scopes commute only up to exchanging them), `ExampleHandles` (the handle counter is shared
  too: two bags without a race on a space). `ExampleNew`: `new` needs an injective supply.
* **Finite answer collection**: `AnswerCollection` keeps completed branches with their constraint
  stores, distinguishes outstanding work from completed emptiness, reopens captured answers against
  one caller at a time, and requires an explicit order before serializing a bag.
* `BinderCore`: the binder core as a fragment at the level of reachable terms; `BinderCoreAnswers`:
  at the level of answers it fails. `NestedCore`: the embeddings of the nested-calls,
  first-order-equations and call-by-need cores, and the first lemmas of their correspondence;
  `ExampleStuckCall`: where the nested-calls core and the language differ (a call that no equation
  answers), and the equation that makes them agree.
* `Laws`, `LawExtension`, `LawDeclarations`, `LawRenaming`: laws that do not depend on the parameters
  (spaces and programs as bags, renaming of bound names, annotated text and its transfer law at the
  move, the elaboration never running computed values, adding an equation whose head is only held as
  data). Their applications and controls: `ExampleTransfer`, `ExampleExtensionApplied`,
  `ExampleRunsAgain`, `ExampleByName`.
* `Example*`: kernel-checked rows for every construct and every clause.
-/
