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
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryMaterializationControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryPhaseControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionContinuationControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshConstructorControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryOutputControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedPortfolioControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementRowsControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedImprovementControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierDriverControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationEntryControls
import Mettapedia.Languages.MeTTa.PeTTa.StreamSourceControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedSourceQualification
import Mettapedia.Machines.ShortestPathRoundsControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PreparedEffectfulQueryControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.OnceQueryControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CollectedOnceQueryControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardContinuationControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLFrontierCleanupControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryContinuationControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedPresenceControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceSourceControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPresenceControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryScanStability
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRowsControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceConditionalControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateBatchControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryGrowthControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRoundControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundPublication
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilWordUpdateControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundAdmissionControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundCompletionControls
import Mettapedia.Machines.CTLUntilFrontierControls
import Mettapedia.Machines.CTLUntilCandidateBagControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQueryControls
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
import Mettapedia.Machines.RootRetirementControls
import Mettapedia.GSLT.Dynamics.RootRetirementInformation
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

Fresh-only phases instead emit nothing for an existing payload. Their count
equals row growth, and zero progress preserves the phase's store. Closed
candidate admission rejects relevant open facts and open captured bindings;
ground output alone does not certify that one-way matching is sufficient.

Source-ordered nested queries read each leg's current state when entered.
Fresh-insertion bodies lift through arbitrary finite nesting and authored
schema phases: their total answer count equals destination row growth.
Zero progress is equivalent to an unchanged state and saturation of every
visited schema, using complete reads at that state. An inner read can see a
row inserted by an earlier outer body; freezing the whole phase loses that
behavior in a checked control. Missing access is not zero progress, and a
private worker's failure does not roll back effects already published by a
native implementation. Finite head bounds and recursive driver adequacy
remain separate obligations.

Insertion followed by an authored continuation has a different return law:
the continuation's answers are returned, not one success per inserted row.
The source bridge preserves this distinction, enters the continuation only
after the new row is visible, and skips it for an already-held row. A complete
two-node recursive source cycle inserts both rows while returning no answers.
Actual fresh insertion receipts decrease the number of unseen heads in a
finite catalogue; support-preserving intervening computations cannot increase
that rank. Finite and infinite fresh-entry paths inherit the bound, without
requiring duplicate-free or catalogue-only stored rows. This does not yet
bound arbitrary callback execution or identify all LUBM dispatch with the
existing finite Horn agenda.

Bound constructor-pattern capture now reads every variable from the actual
incoming substitution. Its structural matcher preserves that entire
substitution and agrees with exact matching of the instantiated literal.
Lookup extensions preserve the captured value. A source guard retains its
authored inert payload, and insertion uses the native raw row-argument slot,
even when the row's constructor also has executable equations. Preparation
requires a complete read, excludes relevant open stored facts and rejects
program declarations and active query forms. This supplies the direct
constructor-shaped insertion body, not its recursive dispatch family.

The conjunctive-output domain is derived from captured values, retained row
coordinates and authored head constants. Actual source substitutions render
only bound output slots. A finite shape/coordinate catalogue encloses those
rows, has an exact sum-of-powers cardinality, and admits a coordinate-wise
membership checker that does not enumerate the catalogue. This discharges
catalogue membership for fresh-entry rank decreases; it does not identify
catalogue size with answer multiplicity or impose catalogue materialization.
An invariant for later reads is still needed to retain one domain throughout
recursive source execution.

Flat source-query legs now exclude the active top-level comma form. The
empty comma query has one witness in both inspected PeTTa references and
must not be compiled as an empty literal relation. Empty IR conjunctions
retain their separate one-witness law. This refusal repairs flat-source
admission; it does not add general active-comma execution to the plain-pattern
batch evaluator model.

A fixed-domain invariant now follows actual mutable reads. Executable
validators inspect the current bindings and each selected space through the
existing closed-row classifier. Domain-safe data insertions preserve these
checks even when they change query answers. The checked head emitter rejects
unbound outputs and program declarations. Its accepted nested execution
refines the existing source worker, preserves ordered results, and supplies
actual completed evaluator derivations. A three-round control yields three,
three and zero fresh insertions in one fixed domain; the final quiet state is
saturated for its schema. The value-domain invariant alone is not a
termination proof for recursive dispatch or a repeated driver.

Those additional obligations are now discharged for the admitted fresh-count
driver grammar. Static slot coverage and a data head establish single-phase
completion. Exact remaining-head balance bounds repeated phases and records
their real counts, including the final zero. Actual clause selection connects
the recursive authored driver to this worker and proves its source call
terminates with true in a saturated state. Renamed drivers and unmatched
equations are supported; a second productive clause or a changed body refuses.
The generic-regime portfolio revalidates current domains, commits the proved
completed observation, and falls back at the exact entrance on exhaustion or
failed validation. Exact source pages decline. This is not arbitrary recursive
callback termination or the full LUBM/SSSP dispatch adapter.

The natural-valued keyed-improvement source block now has a separate actual
PeTTa adapter. It collects the complete current key fibre, distinguishes
absence from one value, and refuses multiple rows, negative or unsupported
values, relevant open facts and missing spaces. Successful execution preserves
the exact remove/add list state and the changed-vertex answer packet. Actual
clause selection admits renamed functions and locals, but rejects additional
productive equations. The generic portfolio keeps the full completed state,
answers and I/O observation, with exact-entrance reference fallback. A native
keyed-map realization, its publication gap and physical cost correspondence
remain separate obligations.

Occurrence-exact functional row lists now refine the logical keyed store.
Actual source matching recovers its zero-or-one fibres, and successful source
updates preserve that representation, untouched row order, other spaces and
state cells. The map projection alone does not recover enumeration order.
Weighted calls evaluate the actual addition operand and refuse a raw candidate
declaration. Their nested current-state execution preserves source answer
occurrences; a completed empty phase certifies unchanged state and complete
nested coverage. Nonnegative weights preserve a captured source label even
across self-loops. This connects individual source updates to min-plus
relaxation. The stream frontend now collects all ordered body effects before
deduplicating the next-frontier packet. Literal superposition evaluates its
branches, while a captured tuple is unpacked without reevaluating its values.
An actual recursive source driver tests that packet, increments its productive
round counter and re-enters its selected clause. Successful private iteration
therefore constructs a completed source call with that exact counter and state.
Duplicate improvements to one vertex remain two producer events even when the
next frontier visits that vertex once. Captures, faults and residual stream
frames have separate positive and negative controls.

The vertex-frontier scheduler has its own finite termination and shortest-path
theorem, with pending-edge/deferred-vertex coverage. Its next frontier alone is
deduplicated; improvement events retain occurrences. Productive rounds and the
final silent round are distinguished. A graph-order control keeps all final
distances but changes the counter from two to three. Weighted path transport
proves distance invariance under support equivalence without identifying
execution order or occurrence-sensitive future deletion. The actual source
driver now reproduces both counter values on the graph-order control. A
general source-graph bridge now covers whole phases with a functional natural
distance relation and a distinct, immutable graph handle. The actual matcher
recovers ordered distance fibres and parallel edge occurrences; source visits
refine the scan with current-state labels, unchanged other spaces and stable
next-frontier deduplication. A concrete authored program instantiates this for
arbitrary finite edge lists. The repeated driver now terminates and returns
the independent weighted-path distances, while retaining its source round
counter and other spaces. Termination restricts the descent to the finite set
of edge targets; the ambient vertex namespace need not be finite. Checked
frontier values, captured query slots and relevant stored rows prevent the
one-way query route from interpreting unsupported open facts as absence.
Mixed graph/distance spaces and native correspondence remain additional
obligations; completed source execution is not a physical-cost theorem.

The frontier entry checker now inspects the actual driver equation and
counter-argument demand. Renamed functions are admitted by their body, not
their spelling. Changed bodies, productive extra equations and raw counters
refuse. The conservative source profile also refuses mixed driver arities:
although wrong-arity clauses cannot match a two-argument call, source loading
can still reject that definition family. An operational clause-filtering law
alone is not evidence that a loader-level change is inert.

Improvement qualification packets are generated from actual selected-clause
certificates and successful private executions. Generic source theorems cover
the closed invocation, collapsed answers and subsequent ordered row query.
Fifteen cases vary function/local names, relation heads, strict/no-op branches
and large integer values. Kernel checks establish qualification and that no
scenario is dropped. Existing text-reader readback is checked by execution,
not claimed as a text-parser adequacy theorem. The reference runner and its
source fixtures are maintained in the project conformance directory.

Prepared nested queries retain ordered substitution occurrences, with a
query-relative validity invariant threaded through every effectful body.
Writes to the same space are permitted when they preserve those query views;
different formula tags give a concrete sufficient condition. A counted
source continuation still sees every producer answer, not merely row growth.
These laws use captured quoted handles and the existing evaluator, not an
unproved whole-program CTL adapter or concurrent snapshot implementation.

A resumable first-query cursor now agrees with the complete source scan's
first occurrence and preserves the residual offset across pauses. Its ledger
counts exactly the visited rows: absence requires the entire captured domain.
At a prepared scoped primitive invocation, first-answer refinement followed
by the maintained once commit takes five control inspections and retains the
older caller frontier and reached world. Literal-Boolean query controls cover
whole scoped entry, collection and effect-preserving resumption. General
body-evaluating match, source operand preparation and native conformance are
not consequences of this local prefix law; row probes are not source fuel.

The closed two-integer query family now starts from actual once/match syntax,
for every ordinary relation name and every represented program. A universal
eleven-control-step completion theorem retains the world, allocator and
private result bindings. A source-fuel-qualified region uses an independently
bounded first-witness probe; a pause or failed closed-candidate check selects
unchanged reference execution. Atom extraction carries exact source identity.
Admission scanning and native work are not bounded by the probe ledger.

The first-witness frame now retains arbitrary satisfiable caller equations,
fresh result and location names, outer alternatives, collected prefixes and
occurrence paths. Its request covers closed plain-query literal patterns,
inert scalar payloads and explicit self/private-space handles. A recursive
recognizer excludes the special cons view at every depth. Top-level comma
patterns are refused here because they denote conjunction, while nested
comma data below an ordinary constructor remains eligible. Exact Atom extraction preserves the
source expression. Prepared reads capture the selected complete domain and
check relevant open candidates. Missing spaces refuse preparation and retain
the reference fault boundary, rather than becoming an empty query.
Actual collapse entry supplies the child-name freshness
from the current control and retained scope inventory. The source child
returns its actual scalar payload or no values without publishing private child answers.
Its return executes the existing generative copy operation: a singleton still
needs an identity, an empty collection does not, and allocation refusal keeps
the completed child and saved caller. After a successful copy, every further
caller page agrees with source execution with the child-control budget paid.
This does not eliminate that allocation or identify the source-control debit
with native work.

The authored not/equality/empty-tuple guard now has a source-prefix theorem
under arbitrary satisfiable caller equations and retained outer scopes. It
delivers a Boolean result constraint to the original caller, with the actual
copy allocator, temporary equations and occurrence paths preserved. Allocation
refusal retains the completed child and caller. The source-control prefix is
20 inspections on a hit and 16 on a miss; this is not a bound on matching,
unification, allocation or native time. A scalar payload such as t or false
is retained by query/collection and forgotten only by the proved presence
consumer. The earlier true-payload laws reuse this constant-payload core.
Closed Boolean not is registered in the ground primitive table; its open
relational input modes are not claimed by this fragment. Whole source-entry
and call composition, still-open patterns, nested body-evaluating matches,
equivalent guard wrappers and the complete CTL loop remain further source
boundaries. The prepared boundary below admits already served operands when
their readings are forced closed by the reached caller equations.

Captured query operands now use one actual principal unifier for location,
pattern and scalar payload. Closed readouts are proved equal in every model
of the reached equations and survive consistent appended constraints;
contradictory extensions fail revalidation. The prepared once-query region
recognizes the actual invocation and choice boundary without rewriting its
control. A bounded witness probe realizes the exact five-inspection source
page. A complete miss removes the branch and executes the remaining four
source inspections, including caller effects. Probe exhaustion, unsupported
operands/rows, missing reads, invalid delimiters and failed return refinement
retain the exact entrance and select reference execution. This admits already
served dynamic space operands and captured pattern variables when their
readings are forced closed; it does not evaluate raw effectful syntax during
capture. Preparation and full-domain checks remain outside the row-probe
budget. The exact page law preserves arbitrary subsequent observations and
does not supply native correspondence or concurrent snapshot stability.

The inspected CTL workload uses CeTTa's extended set-space constructor;
the corrected-stable PeTTa pin e1db30d and the baseline primitive model provide
the zero-argument bag-space constructor. A newer inspected stable-fixed
revision, 6586540, removes that implementation and fails the unchanged
new-space canary. Source-version identities therefore remain explicit;
the pinned check is not newer-branch conformance. The guarded-insertion result supplies
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

The EU source bridge separately proves the ordered frontier/reverse-edge/
satisfaction scan against the candidate bag, retaining all three physical
occurrence coordinates. Prepared query entries construct actual captured
frames from solvable extensions; principal operand transport links successive
captures. Named guard entry retains all selected clauses and the caller's cut
boundary, including witness-copy refusal. The insertion pair supports distinct
satisfaction/frontier handles and preserves an earlier write if the second
target is unavailable. Decoded mixed stores retain original row positions and
unrelated open declarations, with literal-codec formula labels. Successful
extraction supplies exact snapshots and admission to captured query entries.
Appending the next-round publication pair preserves current frontier, graph
and distinct operand reads, but deliberately changes output membership.
Available logical targets now construct the two write receipts and their
actual source execution. Pointwise decoded updates cover aliased and separate
targets; raw satisfaction membership agrees with known-state membership.
A second-target refusal retains the first write and the exact pending request.
Restarting the whole guard after that prefix can omit the unfinished frontier
write, so whole-driver recovery must retain the continuation.
Executable named-conditional admission now checks operand modes, actual clause
selection, principal readings and freshness. Its source-prefix theorem runs
the authored conditional through the first selected guard and restores the
caller before branch selection, preserving other clauses and copy refusal.
It currently recognizes the canonical two-variable guard declaration;
arbitrary declaration alpha-normalization is not supplied by this route.
Checked named-candidate admission now composes one selected guard with the
actual two-write body, one success packet or a held empty branch. It preserves
copy refusal and the pending second write after partial publication. Packet
delivery is collection-local when a parent collector exists. The enclosing
live three-query traversal now retains the actual handle equations and derives
typed store preservation. Its stable query views retain physical positions and
duplicate occurrences. Capture-word decomposition and an exact live guard
decision compose through the existing traversal to the ordered mathematical
fresh list for arbitrary admitted finite graph data. Known and next-frontier
rows retain their old prefixes; identifying the latter with `advance.delta`
requires an initially empty next frontier. Local packet count equals the new
list's length. These completed-round theorems do not assume a final decode or
replace live source execution by a frozen-world executor.
Canonical guard profiles and fresh local slots now establish uniform
no-reference admission, while still permitting explicit suspension. Counting
unowned, non-retired identities gives a source resource theorem: a reserve of
N candidate occurrences plus P initially ready packets constructs round
completion and final scalar-copy success, with exact total identity use N+P.
This is not a native RAM bound or a guarantee for variable-bearing packets.
Named round entry/cleanup and recursive-driver composition, global bindings,
extended set-space construction and EG deletion/absence remain source obligations.

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

Root-retirement evidence now distinguishes current liveness from a cached
mark on an earlier root domain. On a fixed graph, deleting roots preserves
negative marks but may invalidate positive ones. An executable per-root
census and a distinct-contributor ledger give exact incremental subtraction,
including shared cycles, repeated retirement and sequential batches. Its
filtered lookup agrees with collection at the current root domain. These
contributor counts are not native incoming reference counts or path counts.
Old union and retired-provider bitmaps alone cannot determine the new union.

The future observer which may retire arbitrary root identities distinguishes
every contributor subset, giving an exact n-bit interface for n independent
roots. This is a summary-alone bound: a shared root-support index supplies
side information for scalar updates. Neither a per-cell bitmap nor a native
layout is prescribed. Root additions, graph writes, address reuse, foreign
root discovery, physical sweep ordering and callback effects remain separate
correspondence obligations. Collection inhibition alone does not establish
the stability of a previously captured reachability domain.

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
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.ControlComposition
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedQueryAdmission
#foundation_manifest_module Mettapedia.Languages.ProcessCalculi.MORK.MatchLookupLocality
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.SourceRegionExtraction
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedQueryExtraction
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedQueryControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.QuerySetMaterialization
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.QuerySetMaterializationControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryMaterialization
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryMaterializationControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.NestedQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshNestedQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryPhaseSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryPhaseControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionContinuation
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionRank
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionContinuationControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.BoundQueryPattern
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshConstructorSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshConstructorControls
#foundation_manifest_module Mettapedia.GSLT.Dynamics.ConjunctiveOutputDomain
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryOutputDomain
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryOutputControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryDomainInvariant
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryCompletion
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryRank
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryIteration
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryDriver
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedDriverControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryPortfolio
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedPortfolioControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementEntry
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementControls
#foundation_manifest_module Mettapedia.Machines.OrderedKeyedRows
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementRows
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementRowsControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedImprovementSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedImprovementControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedSourceQualification
#foundation_manifest_module Mettapedia.Machines.ShortestPathRounds
#foundation_manifest_module Mettapedia.Machines.ShortestPathRoundsControls
#foundation_manifest_module Mettapedia.Machines.WeightedPathTransport
#foundation_manifest_module Mettapedia.Tools.KernelReflexivity
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryReadStability
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PreparedEffectfulQuery
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PreparedEffectfulQueryControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FirstQueryCursor
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.OncePrimitiveSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ConstantQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.OnceQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.OnceQueryControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryExecution
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryRegion
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryExtraction
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryFrame
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiteralQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CollectedOnceQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CollectedOnceQueryControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQueryOperands
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceQueryRegion
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQueryControls
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
#foundation_manifest_module Mettapedia.Machines.RootRetirementLedger
#foundation_manifest_module Mettapedia.Machines.RootRetirementControls
#foundation_manifest_module Mettapedia.GSLT.Dynamics.RootRetirementInformation
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
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.StreamSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.StreamSourceControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierCollectionSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationRegion
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierDriverControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedQueryRows
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedQueryExecution
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierRefinement
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierDriver
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.CodeSupportAlgebra
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationEntry
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationEntryControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryBagMaterialization
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulTraversal
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageExecution
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardContinuation
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardContinuationControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryBagErasure
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLFrontierCleanupControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalRegion
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverControls
#foundation_manifest_module Mettapedia.Machines.CTLUntilFrontier
#foundation_manifest_module Mettapedia.Machines.CTLUntilFrontierControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryContinuation
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryContinuationControls
#foundation_manifest_module Mettapedia.Machines.CTLUntilCandidateBag
#foundation_manifest_module Mettapedia.Machines.CTLUntilCandidateBagControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedGuardSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedOnceSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedPresenceSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedPresenceControls
#foundation_manifest_module Mettapedia.Logic.LP.UnificationReadSupport
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPatternSupport
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedCollectedOnceSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceSourceControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPresenceSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMutationSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPresenceControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSequence
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryScanStability
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRows
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceCapture
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRowsControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedStore
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedCapture
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCallOperands
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceConditional
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceAdmission
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceConditionalControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionAdmission
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateExecution
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateBatch
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateBatchSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMatchPreparation
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateAdmission
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateBatchControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMatchEntry
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryExecution
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedNestedQuerySource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryGrowth
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilQueryGrowth
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryGrowthControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryPackets
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCollection
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturn
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafPublication
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedCapture
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedFrame
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRound
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundViews
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundPublication
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRoundControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryWordRefinement
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilWordUpdate
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateWords
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundRefinement
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilWordUpdateControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilAdmissionFrame
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafAdmission
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCaptureAdmission
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryAdmission
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundAdmission
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundAdmissionControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.MetavariableFrameStoreCapacity
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarCopyCapacity
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCapacity
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafCompletion
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryWordCompletion
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCopyCapacity
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundCompletion
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundCompletionControls
