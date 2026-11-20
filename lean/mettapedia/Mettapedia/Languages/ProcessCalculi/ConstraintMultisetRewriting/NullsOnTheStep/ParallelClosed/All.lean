import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Calculi
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Presentations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.ContextRuleControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.OwnedStore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.StepSource
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Runs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Separation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.PresentationControl
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Criteria
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.NonEmptyPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.PositiveTell
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Monotone
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Interpreter
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.SharedUnknown
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.FreshOpenings

/-!
# What a neighbour switches off lies outside every calculus whose reduction is closed under parallel contexts

On the step, a composable neighbour can switch reachable success off in two ways: through a
none guard, which reads the whole store (`StepSource`), and, over first-order terms, through a
tell on a variable that the neighbour's knowledge also constrains (`PositiveTell`). Over ground
terms, without none queries and count checks, nothing switches (`Monotone`). With fresh openings, the
second way needs an unknown that the system's start shares with the neighbour (`FreshOpenings`).

* `Calculi`: the algebra. Reduction closed beside, success persisting beside, hence reachable
  success persisting beside; the relation-level theorem (`not_iff_of_switchedOff`); the criterion
  (`UniformTranslation`: homomorphic on parallel composition up to the target's static equivalence,
  preserving and reflecting reachable success) and the separation (`no_uniformTranslation`).
* `Presentations`: every `LanguageDef` with a parallel context rule, read off its declared rules
  (`HasParallelContextRule`), has a reduction closed beside, primitive and modulo equations
  (`closedBeside_contextual`, `closedBeside_moduloEquations`); no relation a parallel component
  switches off is its reduction (`contextual_not_switchedOff`), the none step on patterns among
  them; rho's presentation is an instance. Control: without a context rule the reduction is not
  closed (`Controls.withoutContext_not_closed`).
* `ContextRuleControls`: authorizing the parallel frame is not enough; the loop rule authorizes it
  and its reduction is not closed beside (`withLoop_not_closed`).
* `OwnedStore`: a presentation with one store term and one rule whose freshness premise asks that
  the name `U` occur nowhere in the store term (`ownedStore_step_iff`); it has no parallel context
  rule. Its premise is an occurs check, not a test of rows: a row that mentions `U` without being `U`
  blocks it (`nested_blocks`). No translation of the step into it is stated.
* `Interpreter`: a translation of the none-guarded step into the presentation
  `RuleSyntax.Presentation.wholeStore`, whose one rewrite makes the row `12` where no row is `11`. It
  is a renaming of that one program into its own presentation (`T` and the made row `12` swapped,
  `11` kept) with a check of the knowledge (the row `11` added when the knowledge has an equation with
  distinct sides); it is not an interpreter of the step. With juxtaposition as the target's
  composition, it preserves and reflects reachable success (`interpret_succeeds_iff`) and is not
  homomorphic on parallel composition (`interpret_not_homomorphic`).
* `StepSource`: the step under a program, with the union of configurations as parallel composition
  (disjoint stores, jointly solvable knowledge); a persistent blocker keeps success unreachable
  along every run (`never_succeeds_of_blocker`); the none-guarded program is switchable
  (`source_switchable`). `Runs`: reachability is reachability by the step's own runs.
* `Separation`: no uniform translation of the step with a none-guarded program into any
  presentation with a parallel context rule, into the reduction of any rho rule set, or into
  positive bag rules; one translation violating each target or translation hypothesis singly.
  `PresentationControl`: on a presentation target, homomorphism modulo equations and preservation
  can both hold (the constant translation into a presentation with an idempotence equation).
* `PositiveTell`: the none query is not needed; over first-order terms a program with no check (read a row,
  tell an equation, make a row) is switched off by a neighbour whose knowledge contradicts the tell
  on a shared unknown (`tellSource_switchable`), and the same separations hold for it.
* `Monotone`: for every substitution action, a run of a program without none queries and count checks
  whose firings are each solvable together with a composable neighbour's knowledge is replayed beside
  it (`succeeds_union_of_joint`). Over ground terms that is every run, so success survives every
  composable neighbour (`succeeds_union`), such a program is not switchable (`not_switchable`) and a
  switchable one has a none query or a count check (`switchable_has_none_or_count`, with a
  count-check control `counted_switchable`). A program that fires and is not switchable has a uniform
  translation into a persistent bag calculus (`relayTranslation`): the source hypothesis of the
  separation is needed.
* `SharedUnknown`: over first-order terms, on the step of rule instances (no fresh openings), a
  necessary condition for switching: a switchable program has a rule with a none query or a count
  check, or a switching pair whose every run to success has a firing sharing a variable with the
  neighbour's knowledge (`switchable_has_guard_or_shared`); the positive control `tell_beside_other`.
  The shared variable may be a rule instance's own (`captor_switches`, `captor_on_shared_side`), and
  sharing does not suffice (`friend_shares_and_succeeds`).
* `FreshOpenings`: the line on the step of a program with fresh openings (`RuleSyntax.step`), from
  the private-unknowns results of `RuleSyntax.Scope`: for a positive program and a barb invariant under
  renaming, a composable neighbour (disjoint rows, jointly solvable knowledge) switches reachable
  success off only through an unknown that it and the system's start both mention
  (`switchesOff_shares`); capture cannot happen there (`captor_analog_keeps`), the line is not vacuous
  (`shared_switches`), and it is necessary, not sufficient, for a fixed program (`friend_keeps`) and
  over every positive program (`shared_constrained_never_switches`: a neighbour that repeats the
  system's knowledge shares and constrains its unknown and switches nothing off).
* `NonEmptyPair`: a second none-guarded program, whose rule needs a trigger, separates on a pair
  of non-empty stores; for it the separation holds for translations homomorphic only on pairs of
  non-empty stores.
* `Criteria`: with a context per operator for parallel composition, the separation holds whenever
  the context keeps reachable success of its first hole (`no_compositionalTranslation`); a guarded
  context does not (`Controls.guarded_context`).

The criterion is named in every statement: the characteristic function of success preserves and
reflects reachable success and is not homomorphic on parallel composition
(`Controls.owner_translation`); it decides success instead of translating rows.
-/
