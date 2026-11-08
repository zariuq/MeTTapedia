import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckStability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFreeProcessOrders
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionEndpoints
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPreparationExtensions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommonEventExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationPlan
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusSourceCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualQueryAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCensusPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StagedSourceEffects
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StratifiedCensusCollection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAttemptOutcomes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedPredicateQueryAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClausePublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalScopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalClauses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateClauseResult
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateScheduleCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateAllocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeResult
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StandingRuleMachine
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingEntry
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingScheduler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualParkedContinuations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFallback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseStateRefinement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequenceComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixNativePublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleAllocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleCutRenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseOccurrenceRenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedRowAssembly
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformBirthProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProductionAllocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedScheduleProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalCountQueries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBindingProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeGuardViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSymbolicCountQueries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBirthPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProgramResult
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeInvocation

/-!
# The transform candidate: equations, occurrences and guarded interaction

The atomic kernel on prepared terms is `OccurrenceStep`: a configuration contains an equation
store and a finite set of physical occurrences. A freshened `RuleInstance`
has take, read, tell, check and produce ports. `Selection.Valid` checks their
shape, resource availability, joint consistency and universally entailed
guards; `Selection.result` preserves the surviving occurrences under the same
joint constraints. Equal labels never identify occurrence identities.

Ordinary stored atoms enter through `ContextualStoredRows.store`: their
schematic variables are private, and every selected read or take opens a
fresh whole-atom instance. `Row.shared` explicitly retains shared references;
`Row.schema` can additionally carry declared captures. The raw occurrence
operation below remains the operation on already prepared terms. In
particular, applying its shared profile directly to an unprepared stored atom
does not describe ordinary schematic storage. Per-use opening belongs to
the atomic binding admission, not to an extra resource firing.

`SchematicReach` joins per-use schema opening, reachable spaces, explicitly
shared references and write-only production in one admission on scoped rule
instances. Its located preparation has exactly the existing contextual
activation's equations, physical resources and original schema guard cuts.
In the structural-pattern fragment, this admission constructs a completed
actual solver run. The equation-dependency frame theorem preserves protected
readings as well as unreached physical occurrences. Standing read-only rules
may additionally use propagation history keyed by stable installation and
ordered physical reads; direct queries remain repeatable and consuming
traces are preserved. The profile does not choose source name ownership,
prescribe a physical storage layout or introduce a new evaluator.

`ContextualPublication` gives reusable and shared outputs distinct metadata
in the same completed firing result. Reusable values preserve the actual
solver substitution and freshen their remaining variables on later uses;
shared values retain their original shared reference identities. Their intent
belongs to the production ports, independently of fresh occurrence allocation.
The publication record wraps the existing checked execution. Its reusable
row instances are exactly the original problem/template solution instances,
including when different completed answers introduce different helpers.
Extending the private declaration bank retains existing row matching,
counts, guard semantics and scope coverage. `SchematicReach.realize_publication`
connects that construction to the same located reach admission.
`ContextualTemplateExecution` additionally compiles constructed templates
with private holes and declared actor captures. Its actual publication keeps
those captures shared, with ordinary and shared outputs in the same firing.
`SchematicReachTemplatePublication` retains the located admission. The
instance-observation theorem does not license arbitrary inspection of
internal helper encodings.

`ContextualClausePublication` compiles resolved query/body clauses uniformly.
Query variables, per-use stored-row variables and caller captures have
separate source identities. Their complete joint problem, including body
equations and guards, is embedded into the actual allocated activation.
Source admission and actual compiled publication agree in the established
structural-pattern fragment. Reusable body outputs have exactly the original
source instances; shared outputs retain the returned source environment. That
environment also preserves source instances across helper-family changes
for following bodies. This does not yet compile arbitrary active-expression
episodes or select a textual scope default.

`ContextualConditionalAnswers` gives the value together with an actual update's
remaining equations exactly the original source meaning, without assuming
that the queue has finished. Erasing those obligations can admit a wrong
value. `ContextualConditionalExecution` stores both as one binding unit and
opens them together at each selected read or take. Its joint information
retains incoming constraints, all selected latent equations and body tells.
The actual finite-budget solver return may remain unfinished. Reusable
outputs have exactly the original conditional source instances; shared
outputs retain their references. Admission still requires joint semantic
solvability and the guards at their original cut. An unfinished return alone
does not establish either obligation. Empty latent conditions recover the
earlier semantic admission in both directions. `ContextualConditionalScopes`
preserves coverage of values and heterogeneous equations through the actual
publication, including its fresh private bank and shared captures. This does
not impose a new textual ownership policy, storage layout or authority
primitive. `ContextualConditionalSourceAdmission` extends the independent
resolved-clause source problem with incoming heterogeneous conditions and
the selected rows' latent equations. Its native admission agrees in both
directions; empty conditions recover the earlier source judgment.
`ContextualConditionalClauses` now accepts the conditional world returned
by an earlier clause directly, at any finite solver budget, retaining exact
body instances and the returned source environment. Source clauses can
therefore produce and consume pending answers without a completed-pattern
solution. Arbitrary active expression episodes and collection of conditional
rows remain separate comparisons.

`ContextualConditionalTemplateExecution` extends the constructed-template
publication profile to conditional rows. Its source descriptor carries a
schema body and latent equations in the same private/capture declaration
family. The existing template binding map transports both. The body is
decoded from the actual prepared production; only schema metadata is
installed from the authored descriptor. Ordinary/shared outputs, retained
rows, the physical update and global information use the existing execution.
`ContextualConditionalExecution.Published` is the common pinned execution
record for resolved clauses, direct templates and compiled native bodies.
Each instance fixes its authored rule, selection and output expressions.
Reuse intent explicitly distinguishes a produced-port contract from an
exact flag-function contract. `CompiledTemplate` pairs authored template
data with that same record. Row overlays use `State.withRows`; result-frame
transport and every-model extension are proved once for the base firing.
The publication descriptor remains semantically necessary: the boundary
controls give identical raw executions with different conditional answer
sets and different admission of a following clause. The canonical raw
native target therefore cannot replace the interpreted publication target.
Program composition must retain structured publication data at that boundary.
Every actor model extends through publication, and every result model
projects back. Dormant schema equations are not global obligations.
`ContextualConditionalTemplateState` now constructs the independent source
update for arbitrary incoming row families. `ContextualConditionalTemplateClauses`
uses the existing clause compiler, and its value decoder recovers the actual
published schema body from the prepared output. Source admission and actual
clause compilation agree at every budget; `ContextualConditionalTemplateClauseResult`
preserves actor bindings, physical occurrences and all conditional row
observations with model coverage in both directions.
`ContextualConditionalTemplateSchedules` composes these source clauses with
existing ordinary/shared segments. Its admission compiler retains original
guard cuts, intermediate resource freshness and authored conditional birth
rows with their separate capture transports. The extended grammar is a
compiled native body like the ordinary one, so the common native chain
applies to it, including its original-cut queries.
`ContextualConditionalTemplateOriginSemantics` identifies every final
mixed-body row with its latest authored birth or retained entry, under
port shapes alone. Its lookup reads selections and saved rows, not the
final source store. `ContextualConditionalTemplateInputModels` derives
joint entry-row witnesses for every given final information model.
`ContextualConditionalTemplateAllocation` links those facts to the actual
allocated resource net: each net input is a tracked entry occurrence, and
each net output has a surviving conditional birth with the final row's
meaning. Reused logical identifiers receive distinct bound allocation
names. `ContextualConditionalTemplateNativeProblem` presents the mixed body
as a compiled native body: output-private names have declaration blocks
without global equations for dormant conditions, and the common binding
problem of `ContextualNativeBindingProblem` extends every given source model.
`ContextualConditionalTemplateNativePublicationValues` decodes published
values from the actual produced expressions. The matching and model laws in
`ContextualConditionalTemplateNativeResult` identify the returned world
with the source under the declared row/model observation and bound-name
projection. `ContextualConditionalTemplateEntryCuts` represents every
original cut over entry occurrences and authored prefix creations, with the
same problem, checks and guard meaning, so the common resource and
original-cut queries attach. The mixed `source_iff_native_body` theorem then
characterizes admission by one actual query-admitted firing whose
conditional publication is source-equivalent, and
`source_iff_completed_invocation` adds control consumption. The
guard-boundary control exhibits a refused source body whose
binding/resource producer still executes: the queries are necessary.

`ContextualClauseSourceState` constructs the independent source update
without a native allocation ledger or solver result. `ContextualClauseStateRefinement`
compares the actual compiler target with that state: information, solvability,
physical effects, all conditional row-matching observations and the returned
query environment agree across the actual family extension. Ordinary
schemas, shared references and retained rows are compared separately. The
computed-join control uses a queried lambda body to determine a subsequent
lookup key, then takes a permit and publishes the unique source answer in
one firing. Its competing key has no source or compiled firing. These are
exact conditional-answer comparisons, with no claimed completing budget.
`ContextualWorldComparison` compares source and native worlds through an
exposed environment, model coverage in both directions, and conditional
row observations in all fresh futures. Private declaration families may
differ. Finite row-matching witnesses can be amalgamated without changing
their shared query assignment. Source updates and actual compiler firings
preserve the same comparison, including returned bindings, schemas, shared
references, retained rows and original-world guards.

`ContextualClauseSequences` gives an independent finite authored program
fragment and source/native execution relations. Its `source_iff_native`
theorem, owned by `ContextualClauseSequenceComparison`, preserves the exact
ordered physical selection trace and final conditional return value. Each
native step has an actual worklist computation; no rule calls a whole
source evaluator. The exposed observation profile is explicit. This does
not supply a total automatic guard decision, select a textual scope policy
or impose runtime snapshot copying. Selected ordinary/shared bodies and
mixed bodies with selectively captured productions have the single-firing
comparison below. Complete-census program composition, arbitrary active
evaluator contexts and program-context joins remain open.

`ContextualPrefixIsolation` records a necessary distinction for that fusion:
an earlier reusable schema and an earlier nonbinding check retain their own
information prefix. Independent later constraints do not narrow that prefix
when its private declarations have a separate copy. Its instance and guard
theorems retain arbitrary contextual arities and residual conditions.
`ContextualPrefixNativePublication` constructs an actual bounded solver
result over the separated problems; its stored row has exactly the saved
prefix instances, including with unfinished residual equations. Its guard
asks retain the original watched world. A concrete two-step body publishes
an open schema and later binds the caller: naive final-problem publication
loses an answer, while a corrected single existing firing preserves the
post-state comparison. A final-cut guard may also wrongly discharge an
earlier countermodel.

`ContextualSourceSchedules` represents arbitrary selected private clauses
before admission, including malformed and refused selections. Its compiler
in `ContextualScheduleCompilation` computes explicit binding-equation deltas,
original guard cuts, production origins and a net occurrence precondition
and update. `Schedule.compile_exact` preserves and reflects source admission;
`compile_effect` gives the exact final occurrence set. Earlier production
origins keep their original declarations and conditions, even when later
caller equations change. Native assembly uses the subsequent producer and
query construction; arbitrary evaluator contexts remain a separate comparison.

`ContextualScheduleAllocation` gives internal productions fresh bound
occurrence names while fixing entry occurrences. Its comparison recovers
the exact ordered source selections and final occurrence set by erasure,
and constructs one enabled net commit under the existing freshness rule.
This matters when a source number is reused after consumption: the old
entry occurrence and the new creation cannot be one fresh physical output.
An actual conditional firing repairs the concrete replacement by renaming
only its new creation. No core identity type, source numeric atom, space
handle or query-variable ownership policy is changed. The subsequent native
program construction joins conditional ordinary/shared rows and guards.

`ContextualOccurrenceRenaming` preserves conditional absence and occurrence
counts under an injective physical renaming with corresponding shared rows.
`ContextualScheduleCutRenaming` uses each private prefix's own allocation
map, retaining its information and watched world; all compiled original-cut
guard asks are preserved and reflected. `ContextualClauseOccurrenceRenaming`
retains the exact complete binding problem, including every per-use latent
condition, and the source update's conditional rows at their current names.
Admission is preserved and reflected when the original source freshness is
retained. Actual renamed clause firings exist at every finite solver budget,
and their future row observations agree with the original source update.
These supply the allocation comparisons used by the subsequent body compiler.

`ContextualScheduleOrigins` now compiles the full selected body's row
origins from initial data and authored productions. Retained rows carry
their capture transport, ordinary schemas keep their own saved problem,
and shared values retain the final caller environment. No final source-row
lookup or evaluator callback supplies these origins. The origin theorem
preserves and reflects every conditional row instance across an admitted
body. `ContextualConditionalRowPacking` constructs actual row data in one
private bank, retaining both private equations and shared captures.

`ContextualScheduleRowAssembly` constructs the result's information,
physical store and packed rows from compiled deltas, the renamed net update
and those origins. `ContextualComputedRowAssembly` supplies actual bounded
worklist results for every admitted body and finite budget. The constructed
result preserves source information models, conditional row instances and
returned-value instances. This is a solver-backed result construction,
not yet a proof that the entire body lowers to an ordinary single-clause
native firing. The existing firing graph and history edge types are unchanged.

`ContextualIndependentProblems` places genuinely private condition blocks
in separately tagged families. It extends any selected block model to the
whole problem and preserves its value instances and original guard asks.
`ContextualScheduleBirthModels` proves consistency of every produced
descriptor's creation problem. `ContextualUniformBirthProblem` combines
those private copies with the current caller problem and supplies one
actual bounded solver update. The unchanged ordinary publication
constructor has exactly each birth's original instances. Every given
current caller model extends with its assignment preserved.

This construction excludes arbitrary dormant input conditions and does
not make shared captures independent. A concrete shared-capture example
has globally satisfiable combined conditions yet loses a valid answer at
one caller model. A separate actual native firing publishes two ordinary
outputs together with their different creation freedoms. The subsequent
native program construction joins ordinary/shared body lowering. The
conditional captured-template profile remains a separate obligation.

`ContextualSurvivingProductions` computes each final occurrence's production
index from authored selections. Its ordinary and shared output forms use
the existing publication constructors and one actual update. All rows,
including retained conditional inputs, preserve the source meaning under
the same returned caller environment. `ContextualProductionAllocation`
proves that every physical net output has a surviving production index;
inherited names take the retained-input path, even with source-number reuse.

`ContextualNativeBodies` states the interface of a compiled body (entry
frame, added information, selections, shapes, cuts and their entry
representations, the admission characterization, net inputs and the
publication blocks of its clause kind) and places the original guard
problems in separate private blocks. `ContextualGuardedScheduleProblem`
presents ordinary/shared schedules as compiled bodies. Consistency is equivalent to terminal source
consistency, without assuming successful guards. Joint consistency,
original-world guard views, shapes and resource preconditions preserve and
reflect source admission. Every actual bounded solver return preserves
those guard verdicts, including a countermodel to an earlier guard that a
later caller binding would otherwise erase. The following native views join
equality, absence and count to actual entry data; the native program
construction then joins them with the actual conditional producer.

`ContextualScheduleInputModels` computes which entry schemas the renamed
net inputs actually use. Every terminal source model supplies matching
witnesses for these rows; their private names can be opened together while
retaining that particular caller assignment. Successful guards are not
assumed, and unused stored conditions remain dormant.

`ContextualNativeBindingProblem` constructs, for every compiled body, an explicit declaration frame,
a conditional invocation control row, and the net take/read pattern syntax.
Every given source model extends through the matching equations of the
actual native activation, and every native binding model projects to the
source information. The extra declarations do not narrow the entry
problem, and packed inputs retain their original conditional instances.
The control occurrence is explicit invocation data and is taken by the
firing. Entry preparation is not equality of full inventories. Guard and output
syntax are parameters of this binding comparison. The following native
program construction supplies them from authored cuts and productions.
This comparison fixes the compiled physical selection; it does not
characterize every alternative selection of the raw rule schema.

`ContextualEntryGuardCompilation` computes an entry descriptor for every
authored guard cut. Each contains the prefix resource delta and row origins,
with the exact original problem and checks. All source guard meanings agree,
including under later declaration extensions and before guard admission.
Created identities remain separate from the original input identities.

`ContextualNativeGuardViews` interprets the captures of actual native input
labels in the selected saved-cut block. Every original-cut model extends
through the actual native information, so later bindings cannot remove its
countermodels. Equality uses the existing native guard. Absence splits into
a complete actual-row query for surviving entry inputs and a finite check
of authored prefix creations. The latter is program data, not a replacement
for reading the entry inventory. Together they have exactly the compiled
source absence meaning. The controls distinguish earlier from later cuts,
retain a clause's own tell, detect a matching insertion, permit an unrelated
one, and reject an internal creation missed by an entry-only query.
These are comparisons at the constructed entry world and fixed selection.
The following modules compare count and ordinary/shared publication
meanings. Uniform selected-body firing construction is supplied below;
general program observations still need their join. The capture reset is a declaration
interpretation; it prescribes no physical copying of a parent space.

`ContextualGuardRegression` reuses occurrence-commit exactness for
conditional row matching. Surviving entry matches exclude removals;
created matches are then added, preserving physical multiplicity.
`ContextualGuardEntryViews` constructs the actual row views from input
data and production origins. Their source comparison needs shapes and
resource executability, without successful guards or terminal consistency.
Each current clause retains its own port/tell equations at that comparison.

`ContextualPredicateQueryAdmission` reuses the existing predicate-query
record with typed future assignments. Its native labels include actual
conditional rows and occurrence identities. Marker-only truth queries
describe a captured cut; they do not validate its data dependencies.
A concrete matching-insertion control still passes such a marker while
breaking the intended count. The actual data-region query detects that
insertion and permits an unrelated one.

`ContextualPrincipalCountQueries` translates count guards for an actual
completed principal update to the cardinality of its principal matching
table plus a complete query of the actual row region. Matching persists
under further assignment, and every model factors through that update;
constant all-future counts therefore force that exact table. Completing
unification alone does not complete the query. The concrete native control
keeps two equal conditional schemas as two physical matches and publishes
value 7. This fixed-matching-table translation has a completed-principal
premise; the following symbolic construction does not.

`SymbolicPredicateTable` records conditional row data on finite support,
allowing each future candidate to select a different matching subset.
Its existing predicate query compares recorded and actual matching on
supported identities and excludes matches outside the support. A successful
read reconstructs the actual matching region for arbitrary supplied labels
and worlds. This validates the declared matching observation, not every
possible payload or weighted readout. Constructing support across all
admissible models is semantic and supplies no total matching algorithm.

`ContextualSymbolicCountQueries` joins that read to the actual native binding
information at each original guard cut. The finite count check adds matching
authored creations to surviving entry matches. The conjunction is exactly
the source count guard; any table with a successful actual-data read may
supply it. No completed principal solution is assumed. A concrete unknown
context F with F(0,1)=0 selects different rows under its constant and
projection solutions while its count remains one. No completed principal
update exists, yet an actual firing at every finite worklist budget retains
the equation and publishes the declared value 7. Changing a relevant row or
adding a duplicate matching occurrence invalidates the saved table. Another
control joins the count of box(1) to a clause's own X=1 equation and refuses
the wrong count. Every compiled body, ordinary/shared or mixed, uses these
comparisons below. Program-context comparisons remain open.

`ContextualNativeBirthPublication` joins output instances to the actual
native binding information. Every original instance of an ordinary birth
extends through the selected port equations; conversely every native
instance projects to that birth problem. Later caller constraints do not
narrow its independently scoped variables. An actual conditional firing
with the declared birth output therefore publishes exactly those instances.
Shared outputs use the current caller, and retained input metadata keeps
the original conditional meaning under that same returned environment.
The actual target's equations project to terminal source information and
remain satisfiable. Physical presence is still given by the firing's
resource result, separately from row metadata.

The native control constructs a source-derived ordinary producer for an
earlier box(X) followed by X=1, at every finite solver budget. Its row still
matches box(2), while the returned caller remains X=1. A separate shared
producer accepts box(1) and refuses box(2). These give actual firing
instances of the output laws. The module does not construct the complete
compiler firing uniformly for arbitrary selected bodies. The following
program and invocation modules supply those joins; general program
contexts remain open.

`ContextualNativeProducerProgram` computes the entire production list,
per-occurrence output lookup and publication flags from surviving authored
births. No final source row store supplies the result syntax.
`ContextualNativeProducerAdmission` realizes every body producer with an
actual worklist return at every finite budget. `ContextualNativeResourceQueries`
checks the whole compiled resource precondition against actual required and
forbidden entry identities, retaining freshness of intermediate creations
even when they disappear from the net output. Only port shapes and the
store-independent possibility flag use a point condition. The finite list
in `ContextualNativeProgramGuards` additionally checks every equality,
absence and conditional count at its original cut.

`ContextualNativeProgramExecution` proves, for every compiled body and
producer, that source admission is equivalent to one actual query-admitted
firing. The `source_iff_native_body` theorem in `ContextualNativeProgramResult`
is the joined comparison for ordinary/shared bodies; the mixed theorem of the
same name is in `ContextualConditionalTemplateNativeResult`.
Source admission is equivalent to one actual query-admitted native firing
with the constructed rule, selection, outputs, flags, query list and finite
solver budget. No successful source admission, source shape or resource
validity is assumed on the native side. Its decoded visible world is
`ContextualWorldComparison.Equivalent` to the source result: physical
occurrences, every given information model, returned bindings and future
conditional row-matching observations agree in both directions. Bound
creation names are decoded; the invocation control has been consumed.
Entry preparation and the conditional observation are explicit, rather
than equality for all raw native program observers.

The actual compiler controls cover a stored-lambda computed join followed
by two correlated reads, incompatible reuse, preservation of an earlier
schema, refusal of an earlier guard despite a later tell, and a count at
its clause's own equation cut. An invalid make-then-take prefix has an
enabled net effect but fails the complete source resource condition and
the native absence query. Starting with an empty entry admits that same
internal make/take program. Fresh invocation installation, arbitrary raw selections/program observers and full
active-evaluator/collection composition remain open. No total higher-order
matching or guard-decision algorithm is supplied by semantic query support.

`ContextualNativeInvocation` makes completion linear for every compiled
body using the existing take operation. The invocation control is appended after the data takes,
preserving their opening ordinals and those of the data reads. No output
recreates the control. The joined `source_iff_completed_invocation` theorem
retains actual execution and source-world equivalence while proving control
absence and a strict drop of the pending indicator. Any next admission
requiring that control is impossible, including after arbitrary data steps
that do not produce a control. New control production is an explicit
boundary; global installation, cancellation and retries remain separate
contracts. The actual empty-body control completes at every finite budget
without an administrative replay. A read-gate counterexample permits
arbitrarily many resource executions with unchanged state. Standing-rule
installation policies and the core occurrence identity model are unchanged.

`StandingRuleMachine` joins physical rule installations, ordinary candidate
firings, propagation history, sleeping/waking and scheduler tasks in the
prepared common-interface profile. `StandingRuleRows.valid_iff` compares
the installed body contract with one actual firing that reads its rule.
Installation is an ordinary production; sleeping preserves the world and
the installation. Repeat and once-per-read-selection remain distinct
profiles. A proved reference wake index covers physical and equation-only
changes, and its invariant transfers semantic readiness to the queued task
used by the fairness theorem. Its fixed-interface profile alone does not
identify the distinct private views of contextual schema uses.

`ContextualRuleCode` represents a whole finite rule body as an ordinary
contextual syntax value. Its decoder reconstructs all ports, substitution
commutes with encoding, and every schema use opens the whole body with one
private assignment. A declaration additionally records repetition and
production intents. `ContextualStandingEntry` constructs the operative
source clause from that body, reads its stored declaration in the same
firing and retains the installation. This source entry uses actual
family-changing contextual publication. `ContextualStandingEvents` packages
those actual source and target families. `ContextualStandingScheduler`
constructs a compiler event from independent source readiness, preserves
wake coverage and derives strong-fair recurring firing and weak-fair stable
firing for that source interface. Queued tasks are installation names;
commit witnesses carry their mathematical input indices. Its conservative
reference index rechecks live installations after each public firing. A
native wait index and its costs require a separate refinement; the result
does not prescribe world copying or choose a textual source-scoping policy.

`ContextualParkedContinuations` compiles a linear pending continuation into
an ordinary take in each competing source arm. Its source judgment and
actual compiler invocation agree in both directions. One arm consumes the
shared logical occurrence, and no permitted later event can recreate that
identity. Hence at most one arm can claim it, without fairness assumptions.
Reusable program code remains separate from the pending continuation.

`ContextualSourceCensus` constructs the finite physical candidate coverage
for resolved source alternatives. Its rejection certificates account for
take aliasing, take/read conflicts, actual solver refutations and guard
countermodels. Incoming and per-use latent conditions remain in the whole
source problem. Output allocation does not change source enablement.
Certificate soundness is general; semantic completeness uses the proved
terminating equation fragment and explicit guard countermodels, not a guard
decision oracle. `ContextualFallback` compiles the independently stated
no-primary source judgment and fallback body into actual publication with
that census retained at its entry cut. The body's own equations cannot
retroactively justify fallback. A new matching row excludes it. Whole
reactive source equivalence and deadline arms retain their own comparisons.

Complete queries require more than the fixed five-port restriction.
`PredicateQueryAdmission` extends admission of the same equation/occurrence update
with complete region observations. A query predicate may perform local
matching independently of the caller's substitution; the census must hold
for every joint solution at its original observation cut. Fixed predicates
recover the existing occurrence-commit predicate queries. No queries recovers
exactly the old step. `CensusSourceCompilation` connects the existing complete
source compiler and its independent declarative semantics to this admission,
with retained equations, explicit tells and exact produced bags (or the
source's declared value equality). Its multiset `every` and the separately
compared MM2 set profile retain their different repeated-consumption laws.

`ContextualQueryAnswers` constructs every physical candidate tuple and runs
the existing contextual solver separately for each. A completed table covers
exactly the source matches over all later declaration families. Each answer
factors every original solution, so alternatives are not conjoined and an
open schema need not be enumerated into all ground instances. In the checked
structural-pattern fragment, finite completing budgets exist without a
supplied model. `ContextualCensusPublication` packs the actual returned
families separately and constructs one checked schematic publication of
the complete table. Every physical tuple has its own output; equal values
are not deduplicated. Later matching has exactly the original problem and
template instances. A new matching tuple invalidates the old census. This
table-materialization profile does not by itself compile arbitrary folds
or consuming compound sources. Ordered collections need an ordered scanner
contract; the finite census alone fixes no order.

`StagedSourceEffects` compiles finite source sub-runs over a common prepared
interface, retaining each guard and census at its actual private prefix cut.
Its readiness and final result agree in both directions with that source
execution. Refusal publishes no prefix effects. The retained conditions
cannot be replaced by the bare net effect. Family-changing episodes and a
source expression evaluator require their own compilation bridges.
`StratifiedCensusCollection` connects the existing source query to the role
collection laws, retaining its scanner transcript and complete census.
Collection after the determining constraints is invariant under their
permutation. It imposes no textual source-scoping default.

`ContextualAttemptOutcomes` separates a fired body, certified empty source,
certified refusal and unfinished source search. Nonfiring outcomes retain
the configuration, including a standing installation. A known single answer
does not wait for unrelated jobs; whole-table execution requires completeness
and may fire vacuously. Search and prepared effect interfaces retain their
source-compilation obligation. Semantic exhaustiveness is not a decision
procedure for arbitrary higher-order guards.

For queries that promise order, `OrderedPredicateQueryAdmission` additionally retains
and validates the existing adaptive query program's ordered read transcript
at the firing cut. Its complete reads contribute ordinary census queries;
those queries alone do not recover the order. Validated source rows have
actual candidate firings and exact produced bags. Ordinary unordered queries
do not acquire an ordered-scanner requirement.

The original raw relation and the comparisons below retain their declared
restrictions. For scoped terms, `ContextualGuardedStep.Valid` checks
the actual prepared views, original guards and solvability in any future
declaration family. Within the structural-pattern fragment it is equivalent
to an actual admitted, completed worklist return. `realize_semantic_admission`
constructs the full inventory endpoint and firing from that semantic data;
each actual firing recovers it. `ContextualGuardedStep.Valid` is the older
fixed-family restriction and can reject a solution needing a fresh helper.
Pure arity-preserving declaration extensions preserve and reflect semantic
admission, including output shape and guards at the same original cut.
`ContextualPairFrames.realize_causal_pair` constructs two actual scoped
events from common producer-origin constraints, without supplied solver
returns or paths. A consumer can read or take newly produced shared data;
those uses share the producer's variables instead of freshening them as
schemas. The complete second problem retains the first event's equations.
`realize_ordered_pair` recovers the independently available-input profile.
`realize_two_orders` constructs both orders and preserves and reflects all
final equality, absence and occurrence-count questions over the common event
interface. It retains original and intermediate guard obligations, and is
restricted to independently available inputs in the structural-pattern
fragment. Arbitrary surrounding continuations, joined-schema guards,
mixed-client authority composition and comparison of intermediate effect histories remain
stronger targets. A concrete causal count guard holds before taking its one
matching occurrence and fails afterward; rebasing it to the final world is
an incorrect rejection of a valid execution. Joint inconsistency also does
not erase an already executed prefix.

The independent lambda comparison is a concrete client of these steps.
`LambdaComparison.source_step_iff_executes` realizes every rule of the
context-indexed four-rule lambda source through a completed worklist run.
`LambdaExecution.finite_execution_iff` compares finite source reductions
with a selected semantic transform profile over retained raw endpoints.
The latter carries old equations, shared output terms and scope inventories
across changing binder depths. Every old joint solution extends through a
step. `LambdaExecution.finite_execution_with_solvers_iff` supplies actual
incremental worklist computations along these paths. Completed prefixes
expose each next represented input as a supported pattern problem; raw
compound applications are not silently classified as patterns. This result
does not choose Prime's demanded evaluation policy or supply effects and
sharing from ordinary unrestricted beta reduction.

`ContextualCommunicationAdequacy.source_path_iff_firings` compares finite
paths of the declared intrinsic rho profile with retained occurrence
firings. Its ordinary substitution and optional free Drop must remain
distinct from paper-faithful semantic COMM substitution. The profile
controls show that a public absence observer distinguishes communication
from a later activation stage. `QuotedLambdaRetained.finite_execution_with_solvers_iff`
now supplies the mixed lambda/quotation profile: lexical captures survive,
quotation is inert, and explicit activation runs through the same retained
scope/equation inventories and incremental worklist. Pure lambda paths agree
with the previous client. This is not yet demanded sharing, effects, general
syntax inspection or composition with the communication/query clients.

The theorem below supplies a guarded two-way diamond. Each event is admitted
at its original cut, both sets of equations are jointly consistent, physical
commits are independent, and the other event's writes cannot match an
occurrence-dependent guard. Equations may be nontrivial and share variables.
Resource disjointness alone does not establish these information conditions.
After the diamond, every fixed continuation schedule sees the same solutions
and physical occurrences. The theorem does not erase intermediate effects or
authorize arbitrary rule fusion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Core

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open GuardFreeProcessOrders

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- Independently admitted events can compose when their information and
resource obligations remain compatible. Both executions are constructed. -/
theorem independently_ready_commute
    (first second : ConditionalSchedule.Firing T O) (before : Configuration T O)
    (firstReady : first.2.Valid A label first.1 before)
    (secondReady : second.2.Valid A label second.1 before)
    (resources : Independent label first.2.commit second.2.commit)
    (joint : A.Consistent ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2))
    (firstChecks : ∀ check ∈ first.1.checks,
      Check.IgnoresWrites A ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2)
        label second.2 check)
    (secondChecks : ∀ check ∈ second.1.checks,
      Check.IgnoresWrites A ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2)
        label first.2 check) :
    second.2.Valid A label second.1 (first.2.result label first.1 before) ∧
    first.2.Valid A label first.1 (second.2.result label second.1 before) ∧
    SameUpTo A (second.2.result label second.1 (first.2.result label first.1 before))
      (first.2.result label first.1 (second.2.result label second.1 before)) := by
  have physical := (independent_iff_both_orders firstReady.occurrences secondReady.occurrences).mp resources
  have jointModels (σ : S) :
      A.Models σ ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2) ↔
        A.Models σ ((before.equations ++ added label second.1 second.2) ++ added label first.1 first.2) := by
    simp only [A.models_append]
    tauto
  have secondAfter : second.2.Valid A label second.1 (first.2.result label first.1 before) := by
    refine ⟨secondReady.take_distinct, secondReady.output_distinct, secondReady.take_length,
      secondReady.read_length, secondReady.outputs, physical.1, ?_, ?_⟩
    · simpa only [problem_eq, result_equations] using joint
    · intro check member σ model
      rw [problem_eq, result_equations] at model
      have old : A.Models σ (second.2.problem label second.1 before) := by
        rw [problem_eq]
        exact (A.models_append _ _ _).mpr
          ⟨((A.models_append _ _ _).mp ((A.models_append _ _ _).mp model).1).1,
            ((A.models_append _ _ _).mp model).2⟩
      exact (Check.holds_fire_iff_of_ignored A before.present first.2 check
        (secondChecks check member) σ model).mpr (secondReady.checks check member σ old)
  have firstAfter : first.2.Valid A label first.1 (second.2.result label second.1 before) := by
    refine ⟨firstReady.take_distinct, firstReady.output_distinct, firstReady.take_length,
      firstReady.read_length, firstReady.outputs, physical.2, ?_, ?_⟩
    · rw [problem_eq, result_equations]
      exact (A.equivalent_consistent jointModels).mp joint
    · intro check member σ model
      rw [problem_eq, result_equations] at model
      have original := (jointModels σ).mpr model
      have old : A.Models σ (first.2.problem label first.1 before) := by
        rw [problem_eq]
        exact ((A.models_append _ _ _).mp original).1
      exact (Check.holds_fire_iff_of_ignored A before.present second.2 check
        (firstChecks check member) σ original).mpr (firstReady.checks check member σ old)
  refine ⟨secondAfter, firstAfter, ?_, fire_comm firstReady.occurrences secondReady.occurrences⟩
  intro σ
  simpa only [result_equations] using jointModels σ

/-- Equal endpoint observations preserve admission of arbitrary fixed
continuations, including their later equality, absence and count checks. -/
theorem continuation_after_commuting
    (first second : ConditionalSchedule.Firing T O) (before : Configuration T O)
    (same : SameUpTo A (second.2.result label second.1 (first.2.result label first.1 before))
      (first.2.result label first.1 (second.2.result label second.1 before)))
    (continuation : List (ConditionalSchedule.Firing T O)) :
    ConditionalSchedule.Executable A label
        (second.2.result label second.1 (first.2.result label first.1 before)) continuation ↔
      ConditionalSchedule.Executable A label
        (first.2.result label first.1 (second.2.result label second.1 before)) continuation :=
  executable_congr A label continuation same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Core
