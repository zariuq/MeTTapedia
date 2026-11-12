import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceAnnotated
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceSystemsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceGuardControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FrameFamiliesControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FramedConfigurationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceFootprintControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceRunBoundaries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FramedScopeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ExecutionRectangleAdmissionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.InterchangeTraceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicityControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceMultiplicityControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.GSOSMultiplicity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ExecutionRectangleInterchangeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoherentMonotoneAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResidualRunExchangeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResidualRunClosingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoherentSolutionJoinControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ParallelRunChecksControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ParallelRunControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LocalClosingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ScopedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextPlacementControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorRunsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorDomain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeCoexistenceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderTensorControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderSharedReadsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderFourBlockControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderTraceBoundaryControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperPlacementCoherenceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperBlockTransportControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperRunCompositionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperPlacementIsoControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorInterchangeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperProgramControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperOriginProjectionControls

/-!
# Coexistence objects, frame families and spatial guard laws

This entry exposes the total finite coexistence of native states, common-frame
realization and the actual first-order tensor consumer. Frame families permit
separate original frames without a common native target. Positive guards and
exact solution-relative count conditions remain distinct from admission of
composed executions. No interchange or behavioural congruence is inferred from
the object construction alone.

Joint configurations use the frame-family carrier directly. Their unit and
associativity hold literally and their symmetry preserves solutions. Native
embedding is conservative for solvability. Resource framing has exact freshness
and consumption criteria, and raw identity paths remain distinct from the old
consistent-execution predicate's empty-run domain.

Prepared rectangles have exact criteria for a chosen interleaving, for some
interleaving and for all interleavings, each interpreted in actual dependent
runs. These criteria do not construct a rectangle from arbitrary local runs.
The trace comparison separates canonical residual interchanges from general
similarity and proves that together they present the existing quotient.

Event-indexed bisimulations retain multiplicity and need no finite choice
assumption. Their independent asynchronous congruence transfers through exact
event realizations, with native consumers and an overlap counterexample. The
admitted GSOS profile's set-valued final observation is strictly coarser.

Canonical residual crossing constructs exchange past a complete native run,
with an exact solution-and-resource check and a contextual helper consumer
whose frames grow. Coherent residual solution classes are in bijection with
compatible solution pairs in every future frame. Monotone guards yield an
exact native admission criterion under store growth, without blindness or a
conservative-settlement assumption. Commuting elementary squares identify all
interpreted rectangle paths; equality of complete observations cannot, in
general, establish the elementary equations in reverse.
Four native admissions do not imply a closing isomorphism, and distinct raw
frame codes may have the same term action. Both boundaries have controls.

Complete native-run interchange now uses only its local closing witnesses,
with source-level solution/resource/guard checks for coherent profiles. A
native resource-making control has such an exchange despite lacking a global
closing operation. Scope-key adapters preserve and reflect the original
profile's runs without choosing an inhabitant of the key type.

Actual contextual-helper states realize scoped coexistence. Their local-run
rebase and two-run tensor have exact consistency/freshness domains, preserve
event counts and transport continuations through proved result isomorphisms.
The helper tensor's domain is symmetric and permits overlapping initial
resources. Native controls distinguish shared and isolated declarations,
context-enabled guards, occupied outputs and equal-shaped fresh scopes.

Native coexistence interpretations retain both source maps, including their
scoped family realization when the original frame values coincide. Their
fibres can be empty even though formal coexistence is total. The shared
contextual execution contract constructs whole native runs from candidates,
admission checks and result transport. Its framing domain is separate from
permission. Both the contextual-helper and first-order profiles consume this
implementation, including the two-run constructor. The helper-specific
consistency/freshness domain is retained after migration.

First-order schedules and native runs are in bijection at consistent sources.
The shared construction recovers the existing separated tensor as equality of
complete native runs. Its exact permission test needs the actual guards and
census queries, without blanket blindness. Two local readers can share one
physical occurrence and retain both events; permitted consumption of a shared
occurrence instead fails the unchanged-context framing domain. Raw and
consistent tensor identities retain their distinct definedness conditions.
The first-order framing domain is equivalent both to the resource frame law
and to the native result isomorphism. Selected execution requires only the
role-swap data it uses; involution and source-map naturality are proved as
separate optional certificates for both consumers.

The first-order native trace quotient has an exact presentation on complete
firing words by admitted-pair swaps at their actual prefix states. The older
round equations map into it and can be strictly finer: a count-preserving
replacement commutes natively while failing round write-ignorance. The actual
first-order tensor satisfies four-block interchange in the native trace
category. Its schedule observer fails descent, while event count descends.

For contextual helpers the canonical declaration-swap witness is retained as
data and supplies a closing operation with its cube law. Opposite-side placed
candidates agree with native residuals. The two placement orders commute with
both source embeddings, transport their complete stores and preserve physical
identities. Equal-shaped frames still require the nonidentity declaration
permutation.

Source-compatible placement isomorphisms lift through complete local runs
and both sides of the selected tensor. The shared interpreter constructs
mapped plans, preserves their checks and proves native similarity from the
local covariance laws. Local sequential composition also agrees in the
native trace quotient. Complete declaration blocks, including their grouped
four-block endpoints, have source-compatible placement permutations. Actual
future programs refer to earlier helpers through both permuted embeddings.
Native state equality alone does not establish this compatibility: an identity
view can preserve the whole native state while changing a source variable's
meaning. The source-map controls separate those conditions.

Admitted schedules of the two complete local helper runs now have exactly the
same consistency/freshness domain. Adjacent opposite-side exchanges use the
actual native event square and transport the entire remaining continuation.
The schedule interpreter agrees with the selected TensorPlan.realize, and
sequential schedules agree with native run composition. Together these prove
four-block history interchange for the original contextual tensor, over any
binding signature and helper arities. Given an admitted first tensor stage,
the second stage's exact domain is equivalent to the combined domain.
Two admitted stages therefore construct the whole tensor plan without a
separate whole-plan hypothesis. A higher-order four-block consumer has
distinct raw schedules, related trace arrows, a schedule observation which
cannot descend, an event count which does descend, and a locally admissible
output collision which the joint tensor refuses.

The selected-program contextual profile keeps source roles in its event
fibres. The exact tensor domain supplies every pending event's native
admission and is preserved by execution. Its projection to the asynchronous
component programs is an event-fibre bisimulation, giving parallel
congruence at the declaration-shape observation. Every finite execution
constructs an actual native run, its final placement isomorphism and its
ordered observation. Controls change an output identity, retain distinct
execution orders and distinguish two pending origins from a single local
program. This profile selects admitted local runs; it is not the unrestricted
joint system, where context may enable a locally refused guard.

A separate native control maps distinct source declaration names to the
same constant. Both local candidates are admitted, but their primitive
native firings and endpoints coincide. Source-origin event reindexing
retains them as distinct events, and primitive projection has no origin
readback. Thus an exact event-fibre interpretation requires more than
pointwise preservation of primitive native firings.
-/
