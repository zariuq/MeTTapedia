import Mettapedia.Evidence.SourceScoped
import Mettapedia.GSLT.Dynamics.AnswerDistinctionConservation
import Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission
import Mettapedia.Languages.MeTTa.Prime.CostLayerIterationBoundary
import Mettapedia.Languages.MeTTa.Prime.PolicyKeyNIKAdmission

/-!
# Source-scoped adaptive realization

This module is a small semantic crown over Prime's existing execution-model,
policy-key, evidence-scope, distinction-conservation, and Cost replay theories.
It does not introduce another execution authority.

A prepared realization is semantically admissible only when:

* the retained key supports every declared policy observation;
* the key conserves the distinctions named by its contract;
* its NIK execution admission is current;
* its source scope remains inspectable; and
* exact raw fallback still recovers the complete source execution trace.

Profitability and bounded retention remain separate judgments.  Neither can
establish semantic sufficiency or currentness.  Conversely, a semantically
admissible realization need not be profitable or resident.

The separation follows the source-relative evidence discipline of P. Wang,
the distinction-conservation criterion of F. Heylighen, and the weak-view
factorization order developed in the replay-key and open-ended-context layers.
The Cost instance supplies the concrete proof-history obstruction: compact
term erasure may support selected observations while failing exact replay,
whereas retained elaboration provenance supports every fibre observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.SourceScopedAdaptiveRealization

open Mettapedia.Cybernetics
open Mettapedia.Evidence
open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost.Elaboration
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.PolicyKeyNIKAdmission
open Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uState uPolicy uValue uKey uObservation uSource uArtifact uCost
universe uCandidate uShape uAuthority

/-! ## Four orthogonal judgments -/

/-- A retained key is semantically sufficient for a request when every
requested observation is constant on its fibres.  This is weaker than exact
replay and deliberately says nothing about profitability or residence. -/
def SemanticallySufficient
    {State : Type uState} (request : PolicyRequest State)
    {Key : Type uKey} (key : State → Key) : Prop :=
  ∀ policy, ReplayKey.Supports key (request.observe policy)

/-- The distinctions a representation promises to retain.  Both relations
remain explicit because exact inequality is only one useful contract. -/
structure DistinctionContract
    (State : Type uState) (Key : Type uKey) (key : State → Key) where
  sourceDistinction : State → State → Prop
  keyDistinction : Key → Key → Prop
  conserves :
    Distinction.Conserves sourceDistinction keyDistinction key

/-- Currentness is the existing revision-indexed NIK judgment, exposed under
the adaptive-realization vocabulary rather than reconstructed. -/
def CurrentAt
    {Observation : Type uObservation} {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{uState, uObservation}
      Observation}
    (model : AdmittedExecutionModel dependencies revision source target)
    (currentRevision : dependencies.Revision) : Prop :=
  model.admission.Active currentRevision

/-- A source-scoped currentness receipt.  Its `active` field is indexed by the
exact admitted model, so source identity cannot substitute for authority and
authority cannot erase provenance. -/
structure CurrentSourceAuthorityReceipt
    {Observation : Type uObservation} {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{uState, uObservation}
      Observation}
    (model : AdmittedExecutionModel dependencies revision source target)
    (currentRevision : dependencies.Revision) (Source : Type uSource) where
  sources : Finset Source
  active : CurrentAt model currentRevision

instance currentReceiptSourceScoped
    {Observation : Type uObservation} {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{uState, uObservation}
      Observation}
    {model : AdmittedExecutionModel dependencies revision source target}
    {currentRevision : dependencies.Revision} {Source : Type uSource} :
    SourceScoped (CurrentSourceAuthorityReceipt model currentRevision Source)
      Source where
  sourceScope := CurrentSourceAuthorityReceipt.sources

/-- Bounded retention is a resource-policy judgment over artifacts.  It does
not confer semantic admission on any resident item. -/
structure BoundedRetention (Artifact : Type uArtifact) where
  capacity : Nat
  resident : Finset Artifact
  withinCapacity : resident.card ≤ capacity

/-- Membership in a bounded retention policy. -/
def Retained {Artifact : Type uArtifact} [DecidableEq Artifact]
    (policy : BoundedRetention Artifact) (artifact : Artifact) : Prop :=
  artifact ∈ policy.resident

/-- The existing path-sensitive profitability receipt, named here only as an
orthogonal judgment.  It compares costs after a semantic refinement is
already present; it does not construct that refinement. -/
def ProfitabilityJudgment
    {Candidate : Type uCandidate} {Observation : Type uObservation}
    {family : OptimizationFamily Candidate Observation}
    {dependencies : DependencySystem} {revision : dependencies.Revision}
    {candidate : Candidate}
    (plan : Prepared family dependencies revision candidate)
    (Cost : Type uCost) [Preorder Cost]
    (sourceCost : PathCost (family.source candidate).operational.theory Cost)
    (targetCost : PathCost plan.target.operational.theory Cost) : Prop :=
  PathProfitabilityReceipt plan Cost sourceCost targetCost

/-! ## The semantic admission crown -/

/-- The complete semantic contract for one prepared realization.  The
conclusion retains all witnesses rather than collapsing them to a Boolean
verdict.  Profitability and retention are intentionally absent. -/
structure SemanticallyAdmissible
    {Observation : Type uObservation} {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{uState, uObservation}
      Observation}
    (model : AdmittedExecutionModel dependencies revision source target)
    (request : PolicyRequest (ExecutionTrace target.operational))
    {Key : Type uKey} (key : ExecutionTrace target.operational → Key)
    (view : AdmittedReceiptView model request key)
    (distinctions : DistinctionContract
      (ExecutionTrace target.operational) Key key)
    {Source : Type uSource}
    (receipt : CurrentSourceAuthorityReceipt model currentRevision Source)
    (prepared : model.PreparedTrace) : Prop where
  sufficient : SemanticallySufficient request key
  distinctionsRetained : Distinction.Conserves
    distinctions.sourceDistinction distinctions.keyDistinction key
  observationsAgree : ∀ policy,
    view.evaluate receipt.active prepared policy =
      request.observe policy
        (model.compileTrace receipt.active prepared.sourceTrace)
  fallbackExact :
    model.rawCodec.decode prepared.fallback = prepared.sourceTrace

/-- Policy-key admission, explicit distinction conservation, a current
source-scoped receipt, and exact fallback jointly yield an admissible prepared
realization. -/
theorem admittedReceiptView_semanticallyAdmissible
    {Observation : Type uObservation} {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{uState, uObservation}
      Observation}
    {model : AdmittedExecutionModel dependencies revision source target}
    {request : PolicyRequest (ExecutionTrace target.operational)}
    {Key : Type uKey} {key : ExecutionTrace target.operational → Key}
    (view : AdmittedReceiptView model request key)
    (distinctions : DistinctionContract
      (ExecutionTrace target.operational) Key key)
    {Source : Type uSource}
    (receipt : CurrentSourceAuthorityReceipt model currentRevision Source)
    (prepared : model.PreparedTrace) :
    SemanticallyAdmissible model request key view distinctions receipt
      prepared where
  sufficient := fun policy => view.receiptAdmission.supports policy
  distinctionsRetained := distinctions.conserves
  observationsAgree := fun policy => view.evaluate_eq receipt.active prepared policy
  fallbackExact := prepared.fallback_adequate

/-! ## Cost and occurrence-integrity instances -/

/-- Retaining the proof-relevant Cost elaboration itself is semantically
sufficient for every declared family of observations on that elaboration
fibre. -/
theorem costProvenance_semanticallySufficient
    {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort}
    (request : PolicyRequest (CostOpenElaboration source term)) :
    SemanticallySufficient request
      (provenanceKey (source := source) (term := term)) := by
  intro policy
  exact provenanceKey_supports (request.observe policy)

/-- Finite-support erasure cannot satisfy the exact answer-occurrence
distinction contract: it identifies one occurrence with two. -/
theorem occurrenceSupportErasure_not_exactDistinctionConserving :
    ¬ Distinction.Conserves
      (Distinction.inequality (Multiset Unit))
      (Distinction.inequality (Finset Unit))
      (@bagToSupport.{0}.map Unit) := by
  intro conserves
  obtain ⟨different, collision⟩ := bagToSupport_multiplicity_collision
  exact conserves {()} {(), ()} different collision

/-! ## Controls separating the four axes -/

namespace AliasingCanary

/-- A maximally coarse key on two distinct states. -/
def constantKey : Bool → Unit := fun _ => ()

/-- A policy that intentionally observes no Boolean distinction. -/
def request : PolicyRequest Bool :=
  singlePolicyRequest (fun _ => ()) False

/-- The constant key is sufficient for the declared constant policy. -/
theorem semanticallySufficient :
    SemanticallySufficient request constantKey := by
  intro policy left right _sameKey
  cases policy
  rfl

/-- The same key does not conserve exact state distinctions.  Policy
sufficiency therefore cannot be promoted to proof-state faithfulness. -/
theorem not_exact_distinction_conserving :
    ¬ Distinction.Conserves
      (Distinction.inequality Bool) (Distinction.inequality Unit)
      constantKey := by
  intro conserves
  exact conserves false true (by simp [Distinction.inequality]) rfl

end AliasingCanary

namespace RetentionCanary

def oneSlot : BoundedRetention Bool where
  capacity := 1
  resident := {true}
  withinCapacity := by decide

theorem selected_is_retained : Retained oneSlot true := by
  simp [Retained, oneSlot]

theorem unselected_is_not_retained : ¬ Retained oneSlot false := by
  simp [Retained, oneSlot]

end RetentionCanary

/-- A relevant revision change blocks use of an admitted policy key while its
raw state survives for exact fallback. -/
theorem stale_revision_blocks_activation_and_preserves_fallback :
    (¬ RevisionCanary.admission.Active (true, false)) ∧
      RevisionCanary.prepared.fallback = true :=
  RevisionCanary.relevant_change_prevents_activation_and_preserves_fallback

/-- Reusing a source occurrence on both sides is not source independence,
regardless of payload identity. -/
theorem overlapping_sources_are_not_independent :
    ¬ SourceScoped.Independent SourceScoped.Examples.left
      SourceScoped.Examples.overlapping :=
  SourceScoped.Examples.left_overlapping_not_independent

/-!
The concrete Cost controls are intentionally reused rather than restated:
`rhoCostLayerIteration_compact_collision_forces_decode_failure` exhibits two
distinct proof histories with one compact erasure, while
`rhoCostLayerIteration_provenance_strictlyRefines_compact` proves that the
retained proof-relevant key is strictly more informative.  Likewise,
`bagToSupport_not_distinctionConserving` and
`bagToSupport_multiplicity_collision` are the occurrence-multiplicity gates
for answer readout.
-/

#print axioms admittedReceiptView_semanticallyAdmissible
#print axioms costProvenance_semanticallySufficient
#print axioms occurrenceSupportErasure_not_exactDistinctionConserving
#print axioms AliasingCanary.semanticallySufficient
#print axioms AliasingCanary.not_exact_distinction_conserving
#print axioms stale_revision_blocks_activation_and_preserves_fallback
#print axioms overlapping_sources_are_not_independent
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Elaboration.rhoCostLayerIteration_compact_collision_forces_decode_failure
#print axioms Mettapedia.GSLT.Dynamics.AnswerEffects.bagToSupport_multiplicity_collision

end Mettapedia.Languages.MeTTa.Prime.SourceScopedAdaptiveRealization
