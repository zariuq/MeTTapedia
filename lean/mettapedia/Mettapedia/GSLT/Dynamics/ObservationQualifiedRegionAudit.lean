import Mettapedia.GSLT.Dynamics.RegionObservations
import Mettapedia.GSLT.Dynamics.RegionInformationTransport
import Mettapedia.GSLT.Dynamics.RegionDescriptionFloors
import Mettapedia.GSLT.Dynamics.RegionPortfolio
import Mettapedia.GSLT.Dynamics.PreparedRegion
import Mettapedia.GSLT.Dynamics.RegionCountInstances
import Mettapedia.GSLT.Dynamics.RegionModeInformation
import Mettapedia.GSLT.Dynamics.RegionRepresentation
import Mettapedia.GSLT.Dynamics.RegionProtocolBridge
import Mettapedia.GSLT.Dynamics.SymbolicRegionPortfolio
import Mettapedia.GSLT.Dynamics.ClosureRegionPortfolio
import Mettapedia.GSLT.Dynamics.ImprovementRegionPortfolio
import Mettapedia.GSLT.Dynamics.ConjunctiveRegionProvenance
import Mettapedia.GSLT.Dynamics.GenericJoinRegions
import Mettapedia.GSLT.Dynamics.IndexedJoinRegions
import Mettapedia.GSLT.Dynamics.IndexedTriangleCost
import Mettapedia.GSLT.Dynamics.CyclicJoinRegions
import Mettapedia.GSLT.Dynamics.PreparedFactorIndex
import Mettapedia.GSLT.Dynamics.PreparedJoinLedger
import Mettapedia.GSLT.Dynamics.IndexedJoinDelivery
import Mettapedia.Machines.Cursor.PreparedKeyRuns
import Mettapedia.Machines.StoredIdCandidateRetrieval
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.AggregationPortfolio
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallPortfolio
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryRegionControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQueryControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryIndexedSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedQueryControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.QuerySetMaterializationControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldSurfaceControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldRegionEntryControls
import Mettapedia.GSLT.Dynamics.NestedCTLRegion
import Mettapedia.Logic.BDD.NestedCTLControls
import Mettapedia.Logic.BDD.OperationCache
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLInstructionCodec
import Mettapedia.Languages.OCaml.CompiledDispatchControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.OCamlRegionSourceBridge
import Mettapedia.GSLT.Dynamics.CanonicalStorageRegion
import Mettapedia.GSLT.Dynamics.CollectedReadRegion
import Mettapedia.GSLT.Dynamics.CollectedReadInformation
import Mettapedia.Machines.RegionReadCollectionControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeSourceControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModePortfolioControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldAlgebraPortfolio
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.AccountedFoldControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldPortfolio
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IntegerSortEntry
import Mettapedia.Logic.KernelFoundationManifest

/-!
# Foundation audit for the first observation-qualified region tranche

Layer ownership is explicit: language adapters establish source/profile
meaning; execution realizes query, aggregation and term-machine plans;
storage providers supply representation, occurrence, snapshot and cursor
contracts. Lifetime, publication and resource accounting compose across
those boundaries. Storage choice does not determine language semantics,
and an execution regime does not require one particular physical store.
Optional pushdown kernels retain the same declared relation and observer.

The audit records complete types and transitive axioms for every safe body
owned by these modules, including generated declarations. The source-boundary
check separately rejects direct and transitive PrimeCandidates imports.

The generic interface is instantiated by independent join counts, reversible
occurrence-preserving shape cuts, source-derived additive word operations,
recursive/delta closure, read/erase/put versus upsert, and symbolic fixed-point
pages versus set iteration. Full-response portfolios reuse the indexed cursor
protocol's adaptive-client theorem. Finite mode supplies an exact, nontrivial
future-summary instance; the arbitrary-conjunction module retains polynomial
occurrence provenance at every full assignment. Variable-at-a-time leapfrog
pruning agrees with exhaustive enumeration, and full scheduling preserves and
reflects the ground patterns while weighted evaluation retains derivations.

Indexed two-way ranges refine ordered intersection with binary comparison
charges. An additional minimum-projection probing route refines the arbitrary
join and has a sum-min/logarithmic navigation account over its actual prefixes.
Its source-derived builder discharges range-width and arity bounds; building
the indexes is explicitly outside that navigation account. Triangle ranges
connect actual binary seeks to the degree bound.

Finite information budgets are now attached to the existing semantic
quotients. The least fixed binary width is the ceiling logarithm of the
number of observable classes, including finite quotients of infinite source
syntax. Explicit enumerations construct partial decoders which reject unused
words. Context-indexed codes pay for the largest fibre; reconstructing the
context pays for the disjoint union instead. Operation transports compose
through these codes by checked question translations. An operation which
exposes discarded state cannot use the smaller interface.

Presence under future additions has exactly one bit of semantic information.
Two-label mode under arbitrary additions has no finite sufficient code; a
bounded count family has the exact ceiling-logarithmic budget. Finite CTL
has a valid-state bitmap upper bound, attained when every state predicate is
available. The existing finite-string and Kolmogorov counting theory supplies
worst-case description/program floors for observable classes. None of these
claims identifies minimum physical bytes, amortized runtime, a decoder-free
description length or an algorithm computing shortest programs.

An arbitrary-width cyclic worker now advances only the first cursor, seeks
by binary partition, and rotates the shortened cursor to the end. Its
execution derives its own cyclic-progress trace. Initial head ordering has
a counted comparison ledger; a positional potential bounds productive
advances even when the shortest cursor is not first. Arbitrary conjunctive
queries inherit exact support and occurrence-weighted answers, and the
visited-prefix ledger yields a separate sum-min/logarithmic navigation bound
for this rotating route. Empty projections succeed; empty families and
insufficient fuel retain refusal. Index building and native physical costs
are still separate obligations.

Reusable occurrence-preserving prefix indexes now have executable counted
preparation. Balanced merge sorting charges its actual comparisons, and
adjacent-key grouping retains every occurrence with one comparison per
input boundary. Aligned immutable arrays permit binary positional lookup.
The nested builder has an explicit depth-times-size/logarithmic comparison
bound; queries use at most one logarithmic lookup per level. Completed
indexes retain exactly the source occurrence count at leaves and at most
depth times source size in distinct-key slots. Actual factor patterns supply
constant and repeated-variable lookup coordinates. Indexed leaf weights
compose to the authored conjunction's occurrence interpretation.

Prepared prefix descent now returns the retained next-column key array.
Source-derived conditioning layouts preserve constants, captures and repeated
variables. A complete finite catalogue is built once, with its exponential
factor-arity dependence explicit. Generic cyclic joins use these stored
projections, not source-row rescans. Complete-assignment feasibility reads
the retained leaf's empty/nonempty tag without mapping all occurrence IDs;
the full schedule reaches this indexed branch even at rejected leaves.
Occurrence annotations remain exact for arbitrary commutative weights.
The branch-tree identity charges terminal prefixes as well as internal
ones. Selection tests, descent comparisons, cursor navigation and terminal
lookup have a combined sum-min/logarithmic allowance. Layout comparison
internals, general semiring annotation costs, preparation, physical bytes,
temporary peak memory, revisions and native correspondence remain separately
qualified.

Full occurrence delivery now reuses the resumable Cartesian frontier.
An empty-factor preflight avoids expanding earlier combinations for a failed
assignment. The metered worker charges frame expansion, child-frontier list
passes and copied tuple prefixes, with exact debit composition on resumption.
Complete binding traversal is duplicate-free, while every source occurrence
combination is retained in the delivered bag. Intermediate binding-list
construction and filtering, repeated leaf descent, ID mapping and final
delivery have an explicit fixed-query sum-min/logarithmic-plus-output bound.
This is a declared abstract event ledger, not a native implementation cost
or permission to change an ordered stream. Source PeTTa admission and native
layout correspondence are still separate.

Stored open views have a separate candidate-retrieval bridge. A complete
head screen admits variables and rejects rigid clashes, then the stored-ID
unifier checks every retained occurrence. Exact sweeps preserve duplicates,
order, frames, lazy bindings and paused residuals; split/resumed sweeps agree.
A complete-domain empty sweep proves no finite-term unifier exists. General
semantically complete filters preserve completed answers, but zero-fuel
controls show that this does not preserve paused-work observations. Ground
indexed-join cost bounds are not attached to this open-term route.

Pure PeTTa call-specific extraction now follows actual argument demand and
clause selection, including recursively wrapped scalar operands. Optional
source bodies certify pure empty alternatives without collapsing two answers.
Snapshot-qualified match/collapse/count classifiers preserve row-local frames,
ordered duplicates and exact source result types. Completed-source observations
have their own portfolio; exact source pages still decline these shortcuts.

Read-dependent source certificates additionally compose nested matches,
ordered multi-answer bodies, captured lets, named wrappers, collection,
counts and typed scalar consumers. They retain every consulted snapshot
and all ordered answers. Equal snapshot requirements may be shared; different
snapshots of one handle may not. Stale reads decline, while unrelated state
is carried through unchanged. The actual evaluator supplies completed-source
preservation and reflection. This is bounded call-specific preparation,
which can enumerate many answers, not a cheap symbolic join extractor.
It uses the existing `Eval` profile and does not assert correspondence with
the separate two-way-unifying profile or native concurrent execution.

Flat relation extraction now decodes actual source patterns through a
duplicate-free variable inventory and a literal-value codec. Captured values
must decode exactly rather than becoming unbound slots. The source matcher
and typed row binder agree for every represented input frame, including
repeated variables and captured constraints. A proved mismatch is distinct
from an unsupported row; the latter refuses the entire relation compilation.
Original snapshot-local ordinals survive filtering, and the resulting object
is the existing conjunctive-query Factor. Prepared indexed leaves preserve
its source occurrences and counts at complete assignments. This compiles
rows without enumerating query answers. Compiled legs now compose across
all matches in one captured snapshot: actual substitutions and occurrence
witnesses agree with typed binding execution. The evaluator bridge derives
the nested-match observation and its collapse/size count from actual source
steps. Sequential row binding projects to the independent conjunctive
witness interpretation. A finite domain is now constructed from captured
values and row coordinates. Checked variable coverage prevents unused
inventory slots from inventing source answers. The resulting input proofs
connect source binding to indexed delivery as a complete occurrence bag,
and to weighted counting without enumerating the occurrence product.
The count classifier captures actual caller bindings and a complete snapshot;
missing snapshots, unsupported inputs and exact source-page observers refuse.
Reused certificates recheck their snapshot and decline if it changed. This
does not certify a cheap native revision check, preparation profitability,
arbitrary surrounding effects or concurrent snapshot publication.

The indexed leaf now extracts actual count-query syntax, derives its variable
inventory, and supports captured or qualified quoted space operands. PeTTa
matching, including its cons view, preserves existing handle lookups. A common
source-composition driver follows ordinary wrappers, argument demand, lets,
branches and scalar consumers using source certificates. It does not enumerate
raw query answers when a leaf refuses. Empty and unmatchable equations remain
inert only by actual clause semantics; productive extra answers are retained,
and unsupported effects or raw-argument declarations refuse. Both read-query
and region-composition extractors share one checked fallback executor. Missing
or stale preparation keeps the source entrance, and completed results preserve
and reflect actual source runs. This does not supply native preparation-work
bounds or change the separate effectful-operand continuation contract.

Source-level guarded insertion has a separate effectful certificate. It
preserves captured complete-read absence, the actual success answer, the
updated target rows and other-space/cell frames. Duplicate-free inputs stay
duplicate-free, but successful-call counts do not become stored cardinality.
Missing handles decline, and the data adapter excludes open rows and
equation/declaration writes. A stale-absence counterexample keeps the
concurrency obligation visible.

Captured-query materialization now composes actual stateful source bodies in
order. Matcher locality preserves absence of fresh local names as well as
existing values. A materialization worker projects binding frames to ordered
payload occurrences and omits the private success-answer list, retaining the
original occurrence count. Its completed-state/count observation agrees with
the source, including aliased input/destination spaces. New matching rows do
not extend an already captured query. An empty query need not inspect its
destination, whereas a nonempty query with a missing destination declines.
The worker remains a private-state model: these laws do not license rollback
after native prefix publication.

The inspected CTL workload uses CeTTa's extended set-space constructor;
stable-fixed PeTTa and the current baseline primitive model provide the
zero-argument bag-space constructor. The guarded-insertion result supplies
a baseline source building block, not an operational proof of that extended
constructor or of the complete CTL driver. The workload generator explicitly
adds deadlock self-loops. Its source-visible phase and round counters remain
additional obligations of the CTL adapter.

Captured host-fold semantics now use actual source callback judgments. Natural
inline bodies have a uniform additive source law and whole-driver induction;
named callback preparation retains the ordered trace. Operand preparation uses
the existing evaluator and preserves effects before the specialization boundary.
Refusal after that boundary retains the captured inputs and resulting world.
These are separate host-adapter semantics: the older evaluator's primitive
table still has no fold entry, and no C dispatch correspondence is asserted.

The ordinary PeTTa evaluator now includes the source's registered `msort`
head for closed homogeneous integer and string lists. Integer sorting keeps
duplicates and arbitrary-precision values; Boolean encodings do not qualify
as integer input. The counted merge worker agrees with the primitive's
independent ordered result. Source sorting composes with the captured mode
fold/readout to give the histogram result. Nested size/index consumers use
the actual evaluator. A paid operand receipt keeps effects and the current
world across unsupported-value handoff; it does not restart the operand.
Mixed-value term order and general nested fold dispatch remain outside this
extension, as does a native runtime correspondence theorem.

Typed schema recognition now handles uniform integer minimum/maximum and the
four-field mode callback. Constant Boolean wrappers and reversed order-test
spellings normalize without changing partial evaluation or result sorts.
Mode's source let/readout is connected to histogram aggregation, with sorted
natural input, strict tie-breaking and duplicate votes retained. The original
quoted CDLP forms pass the existing scanner, lexer, parser and Atom reader by
composed transition proofs. Captured-fold portfolios gather ordered, additive,
minimum and maximum candidates. Mode remains a larger readout-region route:
its histogram is not a replacement for the intermediate tuple accumulator.

The retained callback driver now executes actual evaluator steps. Source
debits replay their exact residuals; fold dispatch and return use a separate
host ledger. Admitted folds complete under every positive page quantum, and
completed pages reflect to the independent source fold judgment. A separate
operand receipt counts the two real operand runs and preserves their effects
on callback refusal. Algebraic workers agree in both directions with this
executable callback oracle at the completed-value observation. This does not
install host folds into the older evaluator's primitive table, certify native
choicepoint handoff, or equate source transitions with physical runtime work.

Nested CTL now has independent path semantics, an explicit finite stabilization
budget, total symbolic compilation and exact contextual predicate summaries.
Reduced ordered BDD canonicity justifies semantic keys. Shared instruction tables
refine formula unfolding, and a certified operation cache avoids repeated apply
invocations. The actual workload-opcode codec is syntax-only: it does not certify
the authored PeTTa functions' effects, counts or equation bodies.

Ordered constructor dispatch now refines every CEK page and trace, including
faults and saved continuations. Read-qualified handlers may be reused across
unrelated program changes; changed readings fall back to the current program.
Finite completed evaluations connect to the loaded PeTTa controller's public
readout. Controller search ticks are not identified with source CEK steps.

Bounded structural-cut catalogues preserve ordered occurrences, captured
matching and duplicates. A normalized minimum is selected under an explicit
shared-skeleton cell model. Malformed transfers refuse with the original
rows. This is catalogue-relative, not globally or physically optimal storage.

Nested read-region operations derive roots from pending work, fallback inputs
and returned handles. Arbitrarily scheduled collection preserves complete pages
and the future reads available through the actual returned heap. A local rely
condition includes negative root lookups as well as the live footprint;
payload writes outside it can interleave without changing the region's result.
These are read-operation laws, not a root census for the full native runtime.

For this retained-handle interface, the local rely condition is also
necessary: every reachable cell has an observable finite path witness and
negative root lookups remain dependencies. Collection gives an exact normal
form of the declared future-path observations. Every sufficient reachable
summary determines that normal form; any address-faithful heap preserving
the observations retains at least its allocation set and cell-weight sum.
The result is relative to full-cell/path observation and the current heap
representation, not global physical compression optimality.

The finite dependency census realizes that collector without a classical
reachability decision. Its pages return the reduced heap, preserve future
reads and compose across suspension. Root-slot refusal retains the exact
entrance. Missing root handles are omitted only from the positive census,
not from validity checks. The functional lookup representation can retain
its input heap, so physical allocator release is not inferred from its
registered allocation set.

Still separate: general fold/sort-driver integration and wider source extraction, shared/native
index layout and rotating-cursor correspondence, CTL operational
source admission and native hash-consed DAG realization, general physical
layouts, complete native roots, revision maintenance and publication under
concurrency. The prepared-region check validates a supplied root inventory;
it does not prove that native code supplied every required root. Runtime
speedups and current C qualification are not consequences of this audit.
-/

#foundation_manifest_module Mettapedia.GSLT.Dynamics.RegionObservations
#foundation_manifest_module Mettapedia.InformationTheory.FiniteInterfaceCoding
#foundation_manifest_module Mettapedia.InformationTheory.FiniteDescriptionFloors
#foundation_manifest_module Mettapedia.GSLT.Dynamics.RegionInformationCoding
#foundation_manifest_module Mettapedia.GSLT.Dynamics.RegionInformationTransport
#foundation_manifest_module Mettapedia.GSLT.Dynamics.RegionDescriptionFloors
#foundation_manifest_module Mettapedia.GSLT.Dynamics.RegionPortfolio
#foundation_manifest_module Mettapedia.GSLT.Dynamics.PreparedRegion
#foundation_manifest_module Mettapedia.GSLT.Dynamics.RegionCountInstances
#foundation_manifest_module Mettapedia.GSLT.Dynamics.RegionModeInformation
#foundation_manifest_module Mettapedia.GSLT.Dynamics.RegionRepresentation
#foundation_manifest_module Mettapedia.GSLT.Dynamics.RegionProtocolBridge
#foundation_manifest_module Mettapedia.GSLT.Dynamics.SymbolicRegionPortfolio
#foundation_manifest_module Mettapedia.GSLT.Dynamics.ClosureRegionPortfolio
#foundation_manifest_module Mettapedia.GSLT.Dynamics.ImprovementRegionPortfolio
#foundation_manifest_module Mettapedia.GSLT.Dynamics.ConjunctiveRegionProvenance
#foundation_manifest_module Mettapedia.GSLT.Dynamics.ConjunctiveRowMatching
#foundation_manifest_module Mettapedia.GSLT.Dynamics.ConjunctiveBindingJoin
#foundation_manifest_module Mettapedia.GSLT.Dynamics.ConjunctiveBindingDomain
#foundation_manifest_module Mettapedia.GSLT.Dynamics.ConjunctiveBindingEnumeration
#foundation_manifest_module Mettapedia.GSLT.Dynamics.ConjunctiveBindingObservation
#foundation_manifest_module Mettapedia.GSLT.Dynamics.GenericJoinRegions
#foundation_manifest_module Mettapedia.Machines.Cursor.IndexedIntersection
#foundation_manifest_module Mettapedia.Machines.Cursor.IndexedMultiwayProjection
#foundation_manifest_module Mettapedia.Machines.Cursor.CyclicProgress
#foundation_manifest_module Mettapedia.Machines.Cursor.IndexedCyclicIntersection
#foundation_manifest_module Mettapedia.Machines.Cursor.IndexedCyclicEntry
#foundation_manifest_module Mettapedia.GSLT.Dynamics.CyclicJoinRegions
#foundation_manifest_module Mettapedia.Algorithms.CountedKeySort
#foundation_manifest_module Mettapedia.Algorithms.Compression.ParameterRegionCost
#foundation_manifest_module Mettapedia.Machines.Cursor.ContiguousKeyRuns
#foundation_manifest_module Mettapedia.Machines.Cursor.IndexedKeyLookup
#foundation_manifest_module Mettapedia.Machines.Cursor.IndexedKeyTable
#foundation_manifest_module Mettapedia.Machines.Cursor.PreparedKeyRuns
#foundation_manifest_module Mettapedia.Machines.Cursor.PrefixRunIndex
#foundation_manifest_module Mettapedia.GSLT.Dynamics.PreparedFactorIndex
#foundation_manifest_module Mettapedia.Machines.Cursor.PrefixProjectionIndex
#foundation_manifest_module Mettapedia.GSLT.Dynamics.FactorProjectionLayout
#foundation_manifest_module Mettapedia.GSLT.Dynamics.PreparedJoinRegions
#foundation_manifest_module Mettapedia.GSLT.Dynamics.IndexedJoinLeaves
#foundation_manifest_module Mettapedia.GSLT.Dynamics.PreparedJoinLedger
#foundation_manifest_module Mettapedia.GSLT.Dynamics.IndexedJoinMaterialization
#foundation_manifest_module Mettapedia.GSLT.Dynamics.IndexedJoinDelivery
#foundation_manifest_module Mettapedia.Machines.StoredIdCandidateRetrieval
#foundation_manifest_module Mettapedia.GSLT.Dynamics.IndexedJoinRegions
#foundation_manifest_module Mettapedia.GSLT.Dynamics.IndexedTriangleCost
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.AggregationPortfolio
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallExtraction
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallExtractionControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallPortfolio
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.OptionalCallExtraction
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryRegionExtraction
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryRegionControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyRegionExecution
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQueryExtraction
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQueryControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryRowCodec
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryPatternExtraction
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryRelationCompilation
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryConjunctionCompilation
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQuerySourceExecution
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryIndexedSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.MatchValueExtension
#foundation_manifest_module Mettapedia.Languages.ProcessCalculi.MORK.MatchLookupLocality
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.SourceRegionExtraction
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedQueryExtraction
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedQueryControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.QuerySetMaterialization
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.QuerySetMaterializationControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.FoldSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.FoldSourceBoundary
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldCallbackExtraction
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.AdditiveFoldSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldSurfaceClassifier
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldSurfaceControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldRegionEntry
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldRegionEntryControls
#foundation_manifest_module Mettapedia.Algebra.Order.FiniteSetIteration
#foundation_manifest_module Mettapedia.Logic.CTLFormula
#foundation_manifest_module Mettapedia.Logic.CTLContextualInformation
#foundation_manifest_module Mettapedia.Logic.BDD.BoundedFixedPoints
#foundation_manifest_module Mettapedia.Logic.BDD.NestedCTL
#foundation_manifest_module Mettapedia.Logic.BDD.Canonical
#foundation_manifest_module Mettapedia.Logic.BDD.CTLProgram
#foundation_manifest_module Mettapedia.Logic.BDD.NestedCTLControls
#foundation_manifest_module Mettapedia.Logic.BDD.OperationCache
#foundation_manifest_module Mettapedia.GSLT.Dynamics.NestedCTLRegion
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLInstructionCodec
#foundation_manifest_module Mettapedia.Languages.OCaml.ConstructorDispatch
#foundation_manifest_module Mettapedia.Languages.OCaml.CompiledDispatch
#foundation_manifest_module Mettapedia.Languages.OCaml.CompiledDispatchControls
#foundation_manifest_module Mettapedia.Languages.OCaml.InstructionEquality
#foundation_manifest_module Mettapedia.Languages.OCaml.LiveCompiledDispatch
#foundation_manifest_module Mettapedia.GSLT.Dynamics.OrderedOCamlRegion
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.OCamlRegionSourceBridge
#foundation_manifest_module Mettapedia.Machines.FiniteCutCatalogue
#foundation_manifest_module Mettapedia.Machines.OrderedCutStore
#foundation_manifest_module Mettapedia.GSLT.Dynamics.CanonicalStorageRegion
#foundation_manifest_module Mettapedia.Machines.RegionReadCollection
#foundation_manifest_module Mettapedia.Machines.RegionReadStability
#foundation_manifest_module Mettapedia.Machines.RegionReadCollectionControls
#foundation_manifest_module Mettapedia.Machines.RegionReadInformation
#foundation_manifest_module Mettapedia.Machines.RegionReadCensus
#foundation_manifest_module Mettapedia.GSLT.Dynamics.CollectedReadInformation
#foundation_manifest_module Mettapedia.GSLT.Dynamics.CollectedReadRegion
#foundation_manifest_module Mettapedia.Machines.TypedScalarEquality
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBodyNormalization
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeFoldSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeReadoutSource
#foundation_manifest_module Mettapedia.GSLT.Parsing.SourceScanFinished
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeSourceReplay
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeSourceControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeAggregationPortfolio
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModePortfolioControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ExtremumFoldSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldAlgebraPortfolio
#foundation_manifest_module Mettapedia.Machines.ResumableFinality
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.EvaluatorAccounting
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.PagedFold
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.PagedFoldCompletion
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.PagedFoldLedger
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldAdmission
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldSourceBoundary
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.AccountedFoldEntry
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.AccountedFoldControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldPortfolio
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.StdLib
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.IntegerSortSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.IntegerSortEntry
