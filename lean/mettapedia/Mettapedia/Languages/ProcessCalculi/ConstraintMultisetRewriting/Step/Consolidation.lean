import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProfileControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ModelRefinementControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventEvaluationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedPublicationsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventAccountControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventRecordingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventFeedbackControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventTraceCharge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventTraceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationInitiality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationArticles
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationParserControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSourceRecovery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSourceObservation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationBindingSource
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSchemaControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativeOriginObservationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativeOriginExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RepresentedEffectsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRepresentedNativeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RepresentedPathsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRepresentedRunsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRepresentedHOL
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationQuotedHOL
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationHOLRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.GSOSBehaviour
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunAdmissionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLObserverControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPublications
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameEncodingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.InterfaceTableHosts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DispatchCompose
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceFoundation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLParallelControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedWordControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLTraceControls

/-!
# Transform calculus: shared contracts and interpreted profiles

This entry joins the effect/admission interface, actual event observers and
the authored source interpretations. It is an import boundary, not a claim
that every imported profile has one common evaluator or observation.

* `Interface.Step` supplies semantic refinement without a guard default.
  `Step.Standard` constructs the stronger guarded, literally transported
  profile. Exactness, answer coverage and consistency remain distinct.
* `EventCategory` identifies endpoint-indexed runs with paths in the free
  category. `EventAccountObserver`, `RecordedChoice` and `EscapeEventLifting`
  supply actual recording consumers; `EventTraceRuns` and `EventTraceCharge`
  connect complete paths and lawful readouts to the existing trace quotient.
  `EventFeedbackControls` separates passive recording from execution that
  consults its record: equal stores can then have different permissions.
* `PresentationComposition` elaborates the shared authored transform syntax.
  The occurrence source has concrete state/candidate codecs. Binding-aware
  source execution uses `ProgramBindersInterface` and `PresentationQuotedEvents`.
  Native origins retain publication recipes and explicit catalogue authority.
  Their authored join interprets represented states/candidates, closed under
  prepared results; exact codecs apply to those represented carriers only.
  `RepresentedPaths` makes permitted-candidate coverage and faithful event
  identity separate conditions for whole-path reflection and unique lifting.
  The authored entry has one executable rule, `Execute`, and no process
  constructor for parallel composition. A state is a store; putting two
  stores side by side is their union (`Coexistence.tensor`), and a single
  firing may take occurrences from both parts. A hosted process calculus
  writes `P | Q` in its own syntax and lowers it to that union:
  `RhoStoreBisimulation` proves this for rho on the first-order step.
* `PresentationHOLRuns` and `PresentationQuotedHOL` connect the respective
  source profiles to the loaded admission/path definitions in one received
  model. Empty valid fibres and complete event words remain represented.
  `HOLParallelAgreement` interprets the separately received HOL parallel
  definitions on actual indexed configurations. It constructs a common
  model, retains the earlier definition cache, and proves both loaded
  operations agree with coexistence. Equation lists use the membership
  observation; occurrence identities include an invalid raw sentinel.
  This interpretation covers coexistence, rather than the newer native
  contextual run-interchange contracts.
  `HOLPreparedWordModel` uses the same received history, list interpretation
  and native packet coding as the loaded admission/path operations. Its
  prepared target fold is independent of permission, while its word domain
  is equivalent to a native path with that complete word. Concatenation
  checks the second word at the first word's computed target. The repeated
  tell consumer admits arbitrary finite label words under its explicit
  permission profile and refuses nonempty words under false permission.
  `PresentationRepresentedHOL` supplies the same connection for represented
  source profiles, retaining the semantic event word under path lifting.
  `HOLObserverModel` interprets the loaded pullback on continuation carriers
  and agrees with dependent event recording, retaining empty valid fibres.
  `HOLPublications` applies it to inherited names and fresh success receipts;
  prepared payloads do not require the refused base profile's permission.
* `GSOSBehaviour` is the separately qualified finite-branching, set-observation
  profile. It does not erase multiplicity or reflection from the general core.
* `CoexistenceFoundation` supplies finite families of complete native states,
  frame-family construction, shared-solution realization and the actual
  first-order tensor consumer. Positive spatial guards require no blindness;
  exact counts use the no-new-matching-identity criterion at joint solutions.
  `PreparedEventRuns` reflects permitted proposals into the existing runs.
  Rectangles distinguish one admitted order from all admitted orders;
  constructing compatible residual rectangles is a separate obligation.
  `InterchangeTrace` presents the existing trace equations by canonical
  residual swaps together with similarity, with a strict separating control.
  Native event/run exchange transports continuations across growing frames;
  its check uses the existing coherent residual's compatible solutions.
  `CoherentSolutionJoin` identifies the solution classes with those pairs;
  uniqueness is modulo action on terms. Monotone guards need no blindness
  under store growth. These results assert no pushout of raw frame codes.
  `EventMultiplicity` preserves event fibres, including empty and infinite
  fibres. Its asynchronous congruence transfers through exact realizations;
  native controls distinguish origin erasure and identity overlap. The GSOS
  final set observation is proved strictly coarser. Object coexistence alone
  asserts no execution-interchange law.
  Complete native-run interchange requires local closing data only and has
  exact source-level checks under the coherent-profile contract. The actual
  contextual-helper interpretation realizes two source-local runs, with a
  symmetric consistency/freshness domain, preserved physical identities and
  result isomorphisms across declaration extensions. Scope-key adapters retain
  original preparations, permission and complete native words. These qualified
  consumers supply no automatic composition operation on an opaque native
  state carrier.
  The shared contextual interpreter constructs these helper executions and
  the first-order tensor from local candidate/admission/result laws. Framing
  stability remains distinct from permission. The existing separated tensor
  is recovered as equality of actual native runs, and a shared-read consumer
  demonstrates that disjoint component spaces are unnecessary. Native-pair
  interpretation fibres may be empty; scoped formal coexistence remains
  available. The first-order four-block tensor law now reaches actual native
  traces. Its older round quotient maps into the native quotient and is
  strictly finer for a count-preserving replacement. Order-sensitive readouts
  fail descent while event count descends. Contextual helpers retain the
  canonical swap data, its cube law and both source-embedding equations for
  local placement squares. Source-compatible placement isomorphisms now lift
  through complete local runs and both tensor components, preserving native
  execution and checks. Sequential contextual interpretation agrees with
  native composition. Whole declaration blocks have compatible endpoint
  permutations and actual future programs retain their original source
  references. A native identity view need not preserve those source meanings.
  Complete contextual tensor history interchange now holds in the native
  trace quotient, with its whole plan constructed from two admitted stages.
  Origin-indexed selected programs have contextual event-fibre congruence
  and every finite execution has an actual native realization. Primitive
  firing projection can merge distinct source events; its no-readback
  control prevents that projection from being mistaken for a fibre bijection.

The imported controls distinguish semantic refinement from exactness, prepared
payloads from receipts, execution policy from permission, and successful parse
replay from a complete parse forest. Native implementation refinement is a
separate obligation from these mathematical interpretations.
-/
