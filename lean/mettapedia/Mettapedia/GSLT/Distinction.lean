import Mettapedia.GSLT.Distinction.BehaviouralMetric
import Mettapedia.GSLT.Distinction.BehaviouralMetricControls
import Mettapedia.GSLT.Distinction.GradedCongruence
import Mettapedia.GSLT.Distinction.PathInference
import Mettapedia.GSLT.Distinction.HistoryGrammar
import Mettapedia.GSLT.Distinction.RouteGrades
import Mettapedia.GSLT.Distinction.DemandStrategies
import Mettapedia.GSLT.Distinction.Dictionary
import Mettapedia.GSLT.Distinction.Isometry
import Mettapedia.GSLT.Distinction.RelationalIsometry
import Mettapedia.GSLT.Logic.HennessyMilnerEnumerationMetric
import Mettapedia.GSLT.Logic.EnumerationMetricControls
import Mettapedia.GSLT.Distinction.IsometryControls
import Mettapedia.GSLT.Distinction.BlockTransport
import Mettapedia.GSLT.Distinction.BlockTransportControls
import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.GSLT.Distinction.ProductiveBlocksControls
import Mettapedia.GSLT.Distinction.OrderedSimulation
import Mettapedia.GSLT.Distinction.RelocationRelation
import Mettapedia.GSLT.Distinction.RelocationRelationControls
import Mettapedia.GSLT.Distinction.CausalGluing
import Mettapedia.GSLT.Distinction.CausalGluingControls
import Mettapedia.GSLT.Distinction.HistoryIndependence
import Mettapedia.GSLT.Distinction.SpanTransport
import Mettapedia.GSLT.Distinction.SpanTransportControls
import Mettapedia.GSLT.Distinction.MaterializationObserver
import Mettapedia.GSLT.Distinction.Consolidation
import Mettapedia.GSLT.Distinction.DependentComposition
import Mettapedia.GSLT.Distinction.DependentCompositionIdentity
import Mettapedia.GSLT.Distinction.DependentCompositionControls
import Mettapedia.GSLT.Distinction.SimulationComposition
import Mettapedia.GSLT.Distinction.SimulationCompositionControls
import Mettapedia.GSLT.Distinction.OrderedSimulationSpans
import Mettapedia.GSLT.Distinction.OrderedSimulationSpansControls
import Mettapedia.GSLT.Distinction.ActionCommutation
import Mettapedia.GSLT.Distinction.RunOutcomes
import Mettapedia.GSLT.Distinction.StatusObservers
import Mettapedia.GSLT.Distinction.HistoryObserver
import Mettapedia.GSLT.Distinction.HistoryObserverControls
import Mettapedia.GSLT.Distinction.HistoryTwoSidedObserver
import Mettapedia.GSLT.Distinction.Probabilistic
import Mettapedia.GSLT.Distinction.HistoryCoverage
import Mettapedia.GSLT.Distinction.HistoryContextualReadout
import Mettapedia.GSLT.Distinction.HistoryCappedStage
import Mettapedia.GSLT.Distinction.HistoryCoverageControls
import Mettapedia.GSLT.Distinction.HistoryContextCategory
import Mettapedia.GSLT.Distinction.HistoryContextTwoSided
import Mettapedia.GSLT.Distinction.HistoryContextCost
import Mettapedia.GSLT.Distinction.HistoryCoverageProfiles
import Mettapedia.GSLT.Distinction.HistoryContextControls
import Mettapedia.GSLT.Distinction.HistoryContextHostProfile
import Mettapedia.GSLT.Distinction.DemandStrategiesControls
import Mettapedia.GSLT.Distinction.OptionGraph

/-!
# The distinction calculus over GSLTs, and as GSLTs

The distinction calculus (`Mettapedia.Cybernetics.DistinctionCalculus`) is
generic: observers are similarity kernels on a carrier, and nothing in it
depends on a language runtime.  This layer reads it against GSLTs in both
directions.

**Over GSLTs.**
* `BehaviouralMetric`: a labelled system over a GSLT with observations in
  `[0, 1]` and a discount; the real-valued Hennessy–Milner logic of Desharnais,
  Gupta, Jagadeesan and Panangaden with a supremum diamond; bisimulation
  metrics as prefixed points of the Hausdorff functional and behavioural
  distance as their infimum.  Adequacy always; expressivity and the
  quantitative Hennessy–Milner theorem under finite branching modulo the
  equations; the zero kernel is graded bisimilarity, and for crisp observations
  bisimilarity; `1 −` the distance is a tolerance satisfying the metric law.
* `BehaviouralMetricControls`: without finite branching, logical distance `0`
  against behavioural distance `1`; a graded value `1/2` reached through the
  dynamics; a threshold of the distance that is not transitive.
* `GradedCongruence`: formulas translate along context-stable maps; the
  saturated graded system of an admissible class is a graded congruence (every
  admissible context nonexpansive), its crisp zero kernel is the relative
  equivalence `A.RelEquiv`, and a larger class separates more.  For a monoid of
  contexts with declared consumers, the behavioural distance is the
  all-continuation discrepancy: the calculus's observational end.
* `Dictionary`: that end's zero kernel is the bubble of the privileged word
  behaviour; absolute and weak discernibility as relations of observers.
* `Isometry`: observation-preserving functional bisimulations between graded
  systems preserve formula values; with surjective vocabulary translations they
  preserve logical distances, and, through finite branching of the source
  proved on the image only, behavioural distances; their graphs have zero
  two-sided distortion.  They include covered translations and are forward
  operational translations.  `IsometryControls`: an image-only positive
  instance in a target that is not image-finite, and one counterexample for
  each dropped requirement.
* `BlockTransport`: block readings of a target's own steps (administrative,
  completing, external), blocks as labelled steps, and the compiler interface
  of a path-valued realization whose realized steps are blocks, with block and
  prefix reflection; distances transport, while communication counts stay in
  the realization's account.  `BlockTransportControls`: a four-step and a
  one-step lowering, equal observations with different accounts, primitive
  discounting against blocks, an extra interaction inside and outside the
  observer boundary, and what blocks observe of divergence, deadlock and
  return.
* `ProductiveBlocks`: deterministic machines publishing ordered events, with
  finished, faulted, suspended, stuck and exhausted outcomes; running longer is
  resuming the exact residual, finite observations grow by prefixes, and
  accounts add across resumption.  A rank on administrative steps bounds
  administrative work (also for compiled blocks, through prefix reflection);
  stuck states and silent regions never acquire completion.  Foreign callbacks
  close a machine with visible call, callback and reply events and resume the
  saved continuation.  Cost-bounded simulations relate actual states of two
  machines without being functions, and transport ordered observations.
  `ProductiveBlocksControls`: divergence and deadlock are invisible to blocks
  and visible to the status, restart re-delivers and re-commits while
  resumption does not, undeclared accounts, callbacks erased by an external
  classification, and a checker related to a three-step interpreter.
* `OrderedSimulation`: relations between nondeterministic machines whose
  steps are ordered lists of successor occurrences; related states agree on
  halting and have position-by-position related successors, so complete
  frontiers, pending occurrences and ordered answers are related at every
  fuel; such relations are two-sided and compose, and a commuting map is the
  graph special case.
* `SimulationComposition`: cost simulations compose along the relational
  composite at the product of the costs, with the identity at cost one;
  observations are carried through the composite, final observations
  coincide under the forward simulation alone, backward simulations compose
  in the other order, and along a path through a middle state the middle run
  and outcome are kept as data, without a choice principle.  Completion is
  reflected by a backward simulation, or by the forward simulation with
  progress (related source states never stuck, and a rank decreasing whenever
  the target does not move); reflection composes.  `Stage` is the interface a
  compilation stage discharges, and stages compose.  The composite of the
  segment relations relates segments through a middle segment, lies in the
  segment relation of the composite, and carries the source laws and future
  formulas.  `SimulationCompositionControls`: the product bound is tight and
  the sum fails; a middle stage that stutters silently in a finishing target
  gives a forward composite that does not reflect completion and has no
  progress; a source-only stage likewise; the checker and interpreter reflect
  completion without the backward law; one composite pair through two middle
  states.
* `OrderedSimulationSpans`: successor occurrences as a reduction span; an
  ordered simulation is a one-to-one correspondence of outgoing occurrences,
  hence both source laws of `SpanTransport`, equal numbers of successor
  occurrences, and agreement of every future formula over positions and
  halting.  `OrderedSimulationSpansControls`: a lockstep instance; a doubled
  successor that satisfies both endpoint source laws with no ordered
  simulation; per-branch stuttering that misaligns lockstep frontiers.
* `ActionCommutation`: cross commutation of effect traces and commuting item
  actions of folds are commutation in the monoid of state endomorphisms;
  charging an account is the right action of the coefficients, so the
  interleaving theorem gives the account of every legal interleaving of two
  blocks whose coefficients commute across them.
* `RunOutcomes`: a fuel-indexed run never revises a final outcome, read into the
  cache contract's runs, the machines of `ProductiveBlocks` and the equation
  evaluator; machine outcomes as cache outcomes, recorded exactly when
  finished, and recording exhaustion as refusal is unsound for machines too.
* `StatusObservers`: one builder of a crisp observer from a reading
  (`HennessyMilner.System.withReading`); the status system of a machine is it
  by definition, and the outcome observer of `MaterializationObserver` and the
  return flag of `BlockTransportControls` are equivalent to it.
* `RelocationRelation`: relocation sessions on the reachable graph of a
  finite resource heap: injective on reachable objects, transporting reachable
  cells, relocating registered roots.  Reachability, complete root-path
  observations and aliases are preserved and reflected; every injective copy,
  exact collection and their composites are sessions.
  `RelocationRelationControls`: a missed completion-bank root, garbage
  removal that is many-to-one, one shared world split into two images (no
  session; duplicated admission work; resampled choice), one common session
  across carriers, identifier reuse seen by an old holder, a live owner that
  is not currency, commit retiring the source and refusal rolling back.
* `CausalGluing`: occurrences with logical identities, footprints and observed
  channels on a store that records each cell's writer; independence from the
  read/write hazard and the observation condition, and the swap law keeping the
  store, every reading, each channel's observation, the identities and a
  commutative account (a noncommutative one needs commuting coefficients).  The
  configuration machine fires causal configurations, and two branch runs
  through a common prefix glue exactly when their configurations are
  compatible; the glued run fires the join, its interleavings are one trace,
  and each extension reads what it read in its own branch.  The machine is an
  event concurrency of the shared trace core.  `CausalGluingControls`: shared
  reads glue unobserved and are refused on one ordered channel, equal-payload
  writes conflict, the payload store's fibre, commutative syntax and payload
  deduplication controls, and commuting and noncommuting matrix coefficients.
* `SpanTransport`: relations between reduction spans with four separate
  lifting laws, each exactly one modal transfer of the future diamond or the
  past box; span maps as the functional case, event relations keeping
  readings, labelled tense formulas, parallel occurrences, congruence for
  contexts and substitutions, the two-sided observation with separate
  successor and predecessor branching, stagewise event observations, and
  cost simulations transporting complete runs and future formulas over run
  segments.  `SpanTransportControls`: the future-equal, past-different fibre
  of the forward observer, on a GSLT and on a machine with a simulation each
  way; finitely many successors with infinitely many predecessors; what
  endpoints, labels and occurrences keep of incoming events; an added parallel
  occurrence.
* `MaterializationObserver`: the material readout's kernel is the graded zero
  kernel of the indicator vocabulary under a positive discount and finite
  branching (discount `0` fails); the two-sided readout's kernel is two-sided
  bisimilarity, and it separates the future-equal, past-different terminals.
* `Consolidation`: notions stated twice across these modules, identified
  without changing either statement.  A production ledger's denotation is a
  declared account, so moving a bound production between eager and lazy
  charging is an account move; both are decided by
  `Algebra.OrderedProductCommutation`, exactly by commutation with the block's
  product, and `MovesPast` is the pairwise tile condition, sufficient and not
  necessary.  A sound memo key is constancy on fibres.

**As GSLTs.**
* `PathInference`: the path-inference proof system as a proof-search GSLT;
  a claim runs to the empty obligation list exactly when it is derived, exactly
  when the checker accepts a certificate, and on a finite carrier exactly when
  every metric extension obeys it; proof search is infinitely branching.
* `HistoryGrammar`: the event grammar as a GSLT of configurations; histories
  are labelled paths and traces, a step forgets its event, interleavings of a
  parallel pair differ, copy commutes with merge while the Frobenius laws force
  a subsingleton, local Livšic with fork and erasure, and the three-cycle
  without erasure.
* `HistoryIndependence`: events consume, read and produce nodes; concurrent
  events at a configuration commute, as an event concurrency of the shared
  trace core whose traces keep the bag of events and every commutative event
  cost.  Shared reads commute; a fork and the erasure of the only copy do not.
* `HistoryContextCategory`, `HistoryContextTwoSided`: one context category for
  the history grammar, whose arrows are two-sided event scripts with a renaming
  and a parallel frame, composed as a semidirect product; the grammar over it is
  a two-sided contextual coalgebra with declared result, fault and cost
  readings, whose material equality is one stable bisimulation preserving every
  reading.  The back lifting laws of a context hold exactly when its frame is
  empty (source) and its renaming is moreover onto (target); the predecessor
  box descends along an observation exactly under past matching.
  `HistoryContextCost`: the clamped cost is not congruent for frames, and two
  repairs, a retained potential and neutral contexts, each as one transport
  theorem with its replay criterion.  `HistoryCoverageProfiles`: infinite
  faithful systems over the integer scale never stabilize, and the contextual
  model grows at every world.  `HistoryContextControls`: the kernel is stronger
  than agreement of behaviour, provenance has no material factor, products
  agree now and differ at a future argument, and the future-only profile does
  not descend the predecessor box.  `HistoryContextHostProfile`: the multiset
  history instance, depth transfer and the three coverage profiles.

**Distinction graphs of options.**
* `RouteGrades`: one- and two-sided defects of relational routes, their
  composition, least defects and Łukasiewicz grades over the reals; for a
  category of routes the best grade obeys the Łukasiewicz triangle law and the
  symmetrised best grade is a tolerance on the objects satisfying the metric
  law.
* `DemandStrategies`: eager, lazy and resampling evaluation as options, with
  outcomes, faults and draws; the observer is a weighted family of readings
  given as data.  Discarding and copying are zero and two uses of a bound
  computation, so on computations without faults the agreement facts are the
  generic eager/lazy/resampling laws.  The defect of the default
  interpretation of eager in lazy follows: the weight of bags, counts and
  draws when some computation has other than one answer, the weight of draws
  alone when every computation has exactly one; it changes with the weights
  while the agreement does not.  Exact interpretations exist in every
  direction for every weights and compose; sharing in place of resampling
  needs purity.
-/
