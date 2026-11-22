import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTiming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTimingInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTimingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CommOneFiring
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CommControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CommRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundTwoPresentations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundEveryOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundPetriSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteComm
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteHosting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteBridge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteNested
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteNestedControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.SupportSimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.SupportControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CountedTransitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CountedClasses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CountedFibres
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CountedExample
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNativeRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNativeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNativeUnmatched
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ObservedBags
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ObservedBagsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConventionTame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConventionSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConventionHosting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConventionBridge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConventionControls

/-!
# Relations between step constructions

A step construction is named by five choices: its store, its commit, its guards, its rules and its
knowledge. The one-match step of a program (`RuleSyntax.Core`) is one construction: a bag store, one
match, guards asked after the firing's own tells, a fixed set of rules, one store. Other folders vary
one choice at a time (`JointFirings` the commit, `RuleOccurrences` the rules, the set-store modules the
store). This folder relates constructions to each other.

## When guards are asked

* `AskTiming`: for every guarded step, asking the guards before the firing's own tells is a
  restriction of the step (`beforeTells`), given a split of each firing's information into an ask part
  and its tells. Inclusion always holds; the two timings are equal where the ask part entails the
  tells; the law commutes with every other restriction.
* `AskTimingInstances`: the law for one match, for bags of matches, for every, maximal and unique as
  restrictions, for the set store, for rules held in the store, for worlds and for located knowledge.
  Every, maximal and unique also have a second reading, their quantifiers taken over the matches
  admitted before the tells; it agrees with the first where the ask part entails the tells.
* `AskTimingControls`: strictness for each instance; the two readings of every, maximal and unique are
  incomparable; the split matters; the synchronous reading of a bag is strictly weaker than the joint
  one.

## The F1R3FLY manuscript's COMM on the one-match step

* `CommOneFiring`: one COMM of the manuscript's calculus (`MeTTaCalculus`) is one admitted firing of the
  one-rule program of its redex's shape, under exactly the side conditions of
  `MeTTaOperationsComm.comm_adequacy`; every solution of the result's knowledge reads the made rows as
  the dotted continuations. Also for the corrected step, for open and for non-first-order
  continuations, and the reason `OneFrame.firstOrder_eq` cannot carry the lift.
* `CommControls`: each side condition, dropped, breaks the reading; the manuscript's own example, fired
  and computed.
* `CommRuns`: every run of COMM steps on components is a run of the step of `commRules`, the comm rules
  of every redex shape (one rule per shape, so an infinite program).

The per-shape program is infinite. A finite one follows.

## The F1R3FLY manuscript's calculus by a finite program

* `FiniteComm`: three fixed rules (`program := {commRule, heatRule, clearRule}`) on the single-firing
  step at the one frame of patterns. The comm rule takes two inputs on one channel, tells their
  patterns equal and makes the continuations. Each continuation is represented with its own
  pattern's variables quoted (`predot`), so that the knowledge's unifier reads it as the manuscript's
  dot; the unifier itself is computed by the step.
* `FiniteHosting`: `manuscript_calculus_by_a_finite_program`, the six clauses of
  `reflective_calculus_by_instantiation` for hosted processes, under named conditions: the variable
  convention across parallel parts, ground principal unifiers (`GroundUnifiable` for the sound
  direction), first-order continuations, binary parallel composition.
* `FiniteNested`: the same for continuations that bind at any depth, and runs in both directions.
* `FiniteBridge`: each bag COMM step is a step of the tree's corrected bag semantics.
* `FiniteControls`, `FiniteNestedControls`: each condition, dropped, breaks the correspondence.

The variable convention is without loss of generality for tame processes (next section). Not shown
here: the converse of the bridge, REFL, and the nested fragment without the convention.

## The variable convention is without loss of generality

* `FiniteConvention`: every tame process whose parallel parts are hosted is alpha-equivalent, part by
  part and by the manuscript's own renaming rule, to a hosted process in the form the finite hosting
  assumes (`renaming_into_the_convention`). Every two input parts of the renamed process are apart.
* `FiniteConventionTame`, `FiniteConventionSteps`: on tame bags a COMM respects alpha-equivalence,
  keeps the convention and keeps tameness; every source run up to alpha is matched by a run of the
  single-firing step.
* `FiniteConventionHosting`: the finite hosting without the convention as a hypothesis, for tame
  processes with hosted parts (`manuscript_calculus_without_the_convention`).
* `FiniteConventionBridge`: a step up to alpha is a step of the corrected bag semantics with the
  closing admission.
* `FiniteConventionControls`:
  - a literal hosting that misreads, and the renamed hosting that matches;
  - tameness is necessary;
  - the alternatives fail;
  - the corrected semantics with the admission `conventional` reaches a reduct holding a code (`corrected_step_reaches_a_code`), while with `closing` every step is alpha-equivalent to the manuscript's.

## From a bag store to its set support

* `SupportSimulation`: for programs whose rules all propagate (no takes, no tells, equation guards,
  scoped variables), from settled states, the support map is a stuttering simulation in both
  directions, on steps and on runs; reachable supports are exactly the set store's reachable states
  (`reachable_iff`); completed bag outcomes are the least closure and agree with every discipline's
  terminal set outcome (`completed_outcome_eq`). Divergence is not preserved: the bag store runs
  forever wherever a propagation is enabled (`diverges`), while the set store terminates.
* `SupportControls`: stuttering is necessary; taking one of two copies stutters; taking two copies
  has no set counterpart (`no_support_simulation`); `Scope.Positive` alone does not suffice; reads do
  not separate the stores and counts do.

## An equation written twice answers twice

* `CountedTransitions`: with control rules ambient and each source equation held as an occurrence under
  its list index, the held step has the transitions of the set program (`heldStep_succ_iff`), and each
  firing records an origin; the map from source names to origins is injective without distinct schemas
  (`origin_injective`).
* `CountedClasses`: origin words of held runs are the source's classes; the bag of answers of complete
  runs (`bag_of_held_classes`) and of delivered prefixes is read off held runs by the source's own
  observer `Hosting.Alternatives.classAnswer`, and is the same for every complete run
  (`held_bag_determined`).
* `CountedFibres`: answers counted by origin fibres; the tree's earlier count by distinct schemas is
  recovered as a corollary.
* `CountedExample`: the program with one equation written twice answers `{one, one}` through two origins
  that compete for the same call row (`written_twice_answers`, `written_twice_conflict`); a program
  observing the order of delivery does not descend (`ordered_observer_does_not_descend`).

## Concurrent steps whose firings run in every order

In the field's terms these are multisets of concurrently enabled firings, as in Petri-net step
semantics, whose firings are pairwise compatible, so that every serialization is a run. Compatibility
depends on the configuration: a state-local independence. The axioms of transition systems with
independence are not proved here, and batches admitted only jointly (`Bag.Admits`, the synchronous
reading), which need not start with any single firing, are separate atomic steps, not covered by these
modules. The tree calls the serializable ones rounds (`AnnotatedRuns.Round`, and the runtime's
`step=round`).

* `RoundTwoPresentations`: at one frame, a bag of firings admitted with each member's guards at its own
  information and the base layer's round are one notion for positive rules (`admitsOwn_iff_round`); for
  every rule, exactly when the members ignore each other's writes (`round_image_iff`). No hypothesis on
  the terms of the state.
* `RoundEveryOrder`: the runtime's reading (`RuntimeRound`: every order runs to one result) agrees, on the
  bag store and the set store, for positive rules; every order of such a bag gives one trace.
* `RoundPetriSteps`: every Petri-net step of the base layer (`Race.StepMoves`) is a base round.
* `RoundControls`: absence and count checks separate the three notions; joint freshness is needed;
  ground states are not.

## The hosted named source and the native concurrent rounds

The hosted named source runs on the contextual step, whose frames carry names; the native rounds run on
the native state and its live firings. These modules relate the two through an injective map of frames,
without merging identities.

* `HostedNative`: the adapter from hosted states and canonical firings to the native state and its live
  firings (`state`, `live`, frame map `infoExtension`). Named hypotheses:
  - labels presented at the top sort (`Presented`, supplied at the start and after every step);
  - the rule's unknowns placed injectively, with no collect patterns (`Placed`);
  - canonical openings.
  Proved:
  - the native information is the hosted information carried along the frame map (`information_eq`);
  - a hosted firing is admitted exactly when its live firing is realized, its guards included (`admits_iff`);
  - the frame map identifies no two observations (`info_injective`);
  - the native result extends the hosted result by dead names, at the native result's ledger (`resultExtension`);
  - residuals of a second firing correspond (`residual_eq`, `residual_admits_iff`).
* `HostedNativeRounds`:
  - packet admission for unguarded firings, under the packet construction's shape hypothesis (`packet_admission_iff`);
  - joint solvability on both sides (`jointly_iff`);
  - hosted runs are native sequential runs, up to dead names (`sequential_iff`);
  - for unguarded families that are admitted, pairwise apart and jointly solvable, every order runs and the
    results agree up to dead names (`every_order_of_apart`);
  - without joint solvability, no order runs (`no_order_hosted`).
* `HostedNativeControls`:
  - the program with one equation written twice: its call is admitted and run on both sides;
  - refused firings and an absence guard refuse on both sides;
  - the two origins compete for one call row, so they are not compatible in the packet image;
  - the first-order collapse merges two choice unknowns that the adapter keeps apart;
  - the old ledger admits no extension.

* `HostedNativeUnmatched`, a positive guarded instance: a canonical firing whose rule carries an
  `unmatched` guard.
  - It is admitted on both sides at the state of the hosting control `shared_row_fires`.
  - Under the beside hypotheses, admission holds exactly when no other row matches the call.
  - A private row or a partial match is refused on both sides; with the same rows, the knowledge alone decides.

Not covered here: guarded firings in the packet image, collect patterns, non-canonical openings and
`let`.

## Bags asked at each member's own information

* `ObservedBags`:
  - `ownBagStep`: the bag step restricted to bags admitted with each member's guards at its own information. Its admission is exactly a nonempty bag admitted on its own.
  - `observedOwnStep`: adds region queries per member, read in the member's extended frame and asked at its own information. With no queries it is `ownBagStep`.
  - `ScopedQueries`: queries built only from opened scope terms of the program's rules.
  - `RealizedOn`, `FreshOn`: joint freshness lifted to those scope terms (an empty scope gives back joint freshness).
  - `scopedStep`: the observed step with joint freshness on the scope terms.
  These admissions are atomic. Running members in every order needs, in addition, that each member's queries ignore the others' writes.
* `ObservedBagsControls`: a failing count refuses a bag that the own-guard step admits, and a holding
  count keeps it.
-/
