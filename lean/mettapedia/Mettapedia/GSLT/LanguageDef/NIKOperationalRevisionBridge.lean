import Mettapedia.GSLT.Dynamics.OperationalRevisionWaveAdmission
import Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission

/-!
# NIK admission over revision-scoped operational waves

Semantic dependency revision and runtime store revision answer different
questions.  A NIK artifact remains semantically current when its selected
dependency values agree.  A runtime occurrence remains usable only in the
exact store snapshot that issued its identity.

This module connects the two without identifying them:

* `RevisionedExecution` retains the exact occurrence batch, its store-current
  proof, and the runtime execution witness;
* `runtimeObject` exposes those executions as a proof-relevant indexed
  operational object observed at the runtime state boundary;
* an indexed NIK admission may map source executions into that object;
* `RevisionAlignedWave` pins one mapped source execution to one independently
  certified operational wave; and
* the resulting observation square commutes at every semantically current
  dependency revision.

An irrelevant semantic revision change may reactivate the same retained cell
without changing its runtime wave.  Conversely, a relevant semantic change
blocks NIK activation, while any changed store revision rejects the captured
occurrence batch even when equal payloads remain in the store.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKOperationalRevisionBridge

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.MultiscaleGoal
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.OperationalRevisionWaveAdmission
open Mettapedia.GSLT.Dynamics.TypedValueGeometry
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Machines

/-! ## A runtime execution scoped to one store snapshot -/

/-- A proof-relevant runtime execution whose exact occurrence identities all
resolve in one captured store view. -/
structure RevisionedExecution
    {StoreId StoreRevision Entry : Type}
    [DecidableEq StoreId] [DecidableEq StoreRevision]
    {State StateView : Type}
    (view : RevisionedStoreView StoreId StoreRevision Entry)
    (semantics : ExecutionSemantics
      (RevisionedOccurrence StoreId StoreRevision Entry) State StateView)
    (source target : State) where
  batch : List (RevisionedOccurrence StoreId StoreRevision Entry)
  current : CurrentBatch view batch
  run : semantics.run source batch target

namespace RevisionedExecution

variable {StoreId StoreRevision Entry : Type} [DecidableEq StoreId]
variable [DecidableEq StoreRevision]
variable {State StateView : Type}
variable {view : RevisionedStoreView StoreId StoreRevision Entry}
variable {semantics : ExecutionSemantics
  (RevisionedOccurrence StoreId StoreRevision Entry) State StateView}
variable {source target : State}

/-- Runtime execution observation is the declared observation of its terminal
state.  The occurrence batch remains available independently. -/
def observation
    (_execution : RevisionedExecution view semantics source target) :
    Option StateView :=
  some (semantics.observe target)

end RevisionedExecution

/-- The runtime at one store snapshot, regarded as a proof-relevant indexed
operational object.  Its meaning fibre is an authored state invariant. -/
def runtimeObject
    {StoreId StoreRevision Entry : Type}
    [DecidableEq StoreId] [DecidableEq StoreRevision]
    {State StateView : Type}
    (view : RevisionedStoreView StoreId StoreRevision Entry)
    (semantics : ExecutionSemantics
      (RevisionedOccurrence StoreId StoreRevision Entry) State StateView)
    (invariant : State -> Prop) :
    IndexedObservedOperationalObject StateView where
  operational :=
    { State := State
      Execution := RevisionedExecution view semantics
      Meaning := invariant }
  observe := fun execution => execution.observation

/-! ## Operational admissions provide concrete revisioned executions -/

namespace RuntimeWave

variable {StoreId StoreRevision Entry : Type} [DecidableEq StoreId]
variable [DecidableEq StoreRevision]
variable {Guard CandidateView State StateView Account Cost Value : Type}
variable [AddMonoid Account]
variable {Delta InvariantReceipt : Type}
variable {view : RevisionedStoreView StoreId StoreRevision Entry}
variable {contract : Contract
  (RevisionedOccurrence StoreId StoreRevision Entry) Guard CandidateView}
variable {semantics : ExecutionSemantics
  (RevisionedOccurrence StoreId StoreRevision Entry) State StateView}
variable {initial referenceTarget : State}
variable {demand : RevisionedOccurrence StoreId StoreRevision Entry -> Account}
variable {sourceAccount : Account}
variable {batch : List (RevisionedOccurrence StoreId StoreRevision Entry)}
variable {problem : ProblemSpace State} {cost : State -> Cost}
variable {value : State -> Value} {geometry : ValueGeometry Value}
variable {error : Real} {invariant : State -> Prop}

/-- The reference schedule retained by a certified operational wave is a
revision-scoped proof-relevant runtime execution. -/
def referenceExecution
    (admission : OperationalAdmission Delta InvariantReceipt view contract
      semantics initial referenceTarget demand sourceAccount batch problem
      cost value geometry error invariant) :
    RevisionedExecution view semantics initial referenceTarget where
  batch := batch
  current := admission.current
  run := admission.certified.executionSerializable.1

/-- A changed store revision invalidates the complete nonempty admitted batch,
not merely one selected representative. -/
theorem noCurrentBatchAfterStoreRevisionChange
    (admission : OperationalAdmission Delta InvariantReceipt view contract
      semantics initial referenceTarget demand sourceAccount batch problem
      cost value geometry error invariant)
    (nextRevision : StoreRevision) (nextEntries : List Entry)
    (changed : nextRevision ≠ view.revision) :
    Not (CurrentBatch (view.replaceRevision nextRevision nextEntries) batch) := by
  intro replayCurrent
  obtain ⟨occurrence, member⟩ :=
    List.exists_mem_of_ne_nil batch admission.certified.nonempty
  have rejected := admission.occurrence_rejected_after_revision_change member
    nextRevision nextEntries changed
  have resolved := (replayCurrent occurrence member).resolves
  rw [rejected] at resolved
  cases resolved

/-- Even identical replacement payloads cannot construct a new operational
admission over occurrence identities issued by the old store revision. -/
theorem noReplayAfterStoreRevisionChange
    (admission : OperationalAdmission Delta InvariantReceipt view contract
      semantics initial referenceTarget demand sourceAccount batch problem
      cost value geometry error invariant)
    (nextRevision : StoreRevision) (nextEntries : List Entry)
    (changed : nextRevision ≠ view.revision) :
    Not (Nonempty
      (OperationalAdmission Delta InvariantReceipt
        (view.replaceRevision nextRevision nextEntries) contract semantics
        initial referenceTarget demand sourceAccount batch problem cost value
        geometry error invariant)) := by
  rintro ⟨replay⟩
  exact noCurrentBatchAfterStoreRevisionChange admission nextRevision
    nextEntries changed replay.current

end RuntimeWave

/-! ## The semantic-currentness / store-currentness bridge -/

/-- One source execution mapped by a retained NIK cell to the exact batch of
an independently certified operational wave.

The NIK admission supplies semantic dependency currentness and the
observation-preserving execution map.  The operational admission supplies
candidate, schedule, resource, geometric, invariant, and handler evidence.
The endpoint and batch equations are the explicit weld between them. -/
structure RevisionAlignedWave
    {StoreId StoreRevision Entry : Type}
    [DecidableEq StoreId] [DecidableEq StoreRevision]
    {Guard CandidateView State StateView Account Cost Value : Type}
    [AddMonoid Account]
    {Delta InvariantReceipt : Type}
    {view : RevisionedStoreView StoreId StoreRevision Entry}
    {contract : Contract
      (RevisionedOccurrence StoreId StoreRevision Entry) Guard CandidateView}
    {semantics : ExecutionSemantics
      (RevisionedOccurrence StoreId StoreRevision Entry) State StateView}
    {initial referenceTarget : State}
    {demand : RevisionedOccurrence StoreId StoreRevision Entry -> Account}
    {sourceAccount : Account}
    {batch : List (RevisionedOccurrence StoreId StoreRevision Entry)}
    {problem : ProblemSpace State} {cost : State -> Cost}
    {value : State -> Value} {geometry : ValueGeometry Value}
    {error : Real} {invariant : State -> Prop}
    {dependencies : DependencySystem} {admittedRevision : dependencies.Revision}
    {sourceObject : IndexedObservedOperationalObject StateView}
    (semanticAdmission : IndexedObservedAdmittedAt dependencies admittedRevision
      sourceObject (runtimeObject view semantics invariant))
    (operationalAdmission : OperationalAdmission Delta InvariantReceipt view
      contract semantics initial referenceTarget demand sourceAccount batch
      problem cost value geometry error invariant)
    (currentRevision : dependencies.Revision) where
  semanticActive : semanticAdmission.Active currentRevision
  sourceStart : sourceObject.operational.State
  sourceTarget : sourceObject.operational.State
  sourceExecution :
    sourceObject.operational.Execution sourceStart sourceTarget
  mapsInitial :
    semanticAdmission.refinement.refinement.mapState sourceStart = initial
  mapsTarget :
    semanticAdmission.refinement.refinement.mapState sourceTarget =
      referenceTarget
  mapsBatch :
    (semanticAdmission.refinement.refinement.mapExecution
      sourceExecution).batch = batch

namespace RevisionAlignedWave

variable {StoreId StoreRevision Entry : Type} [DecidableEq StoreId]
variable [DecidableEq StoreRevision]
variable {Guard CandidateView State StateView Account Cost Value : Type}
variable [AddMonoid Account]
variable {Delta InvariantReceipt : Type}
variable {view : RevisionedStoreView StoreId StoreRevision Entry}
variable {contract : Contract
  (RevisionedOccurrence StoreId StoreRevision Entry) Guard CandidateView}
variable {semantics : ExecutionSemantics
  (RevisionedOccurrence StoreId StoreRevision Entry) State StateView}
variable {initial referenceTarget : State}
variable {demand : RevisionedOccurrence StoreId StoreRevision Entry -> Account}
variable {sourceAccount : Account}
variable {batch : List (RevisionedOccurrence StoreId StoreRevision Entry)}
variable {problem : ProblemSpace State} {cost : State -> Cost}
variable {value : State -> Value} {geometry : ValueGeometry Value}
variable {error : Real} {invariant : State -> Prop}
variable {dependencies : DependencySystem}
variable {admittedRevision currentRevision nextRevision : dependencies.Revision}
variable {sourceObject : IndexedObservedOperationalObject StateView}
variable {semanticAdmission : IndexedObservedAdmittedAt dependencies
  admittedRevision sourceObject (runtimeObject view semantics invariant)}
variable {operationalAdmission : OperationalAdmission Delta InvariantReceipt
  view contract semantics initial referenceTarget demand sourceAccount batch
  problem cost value geometry error invariant}

/-- The runtime execution produced by the retained NIK cell. -/
def mappedExecution
    (bridge : RevisionAlignedWave semanticAdmission operationalAdmission
      currentRevision) :
    RevisionedExecution view semantics
      (semanticAdmission.refinement.refinement.mapState bridge.sourceStart)
      (semanticAdmission.refinement.refinement.mapState bridge.sourceTarget) :=
  semanticAdmission.refinement.refinement.mapExecution bridge.sourceExecution

/-- The mapped source execution uses exactly the independently certified
runtime occurrence batch. -/
theorem mappedExecution_batch
    (bridge : RevisionAlignedWave semanticAdmission operationalAdmission
      currentRevision) :
    bridge.mappedExecution.batch = batch :=
  bridge.mapsBatch

/-- The mapped execution really runs the certified batch between the named
operational endpoints. -/
theorem mappedExecution_runs
    (_bridge : RevisionAlignedWave semanticAdmission operationalAdmission
      currentRevision) :
    semantics.run initial batch referenceTarget :=
  operationalAdmission.certified.executionSerializable.1

/-- Before endpoint transport, the mapped execution itself retains its exact
runtime run witness. -/
theorem mappedExecution_has_run
    (bridge : RevisionAlignedWave semanticAdmission operationalAdmission
      currentRevision) :
    semantics.run
      (semanticAdmission.refinement.refinement.mapState bridge.sourceStart)
      bridge.mappedExecution.batch
      (semanticAdmission.refinement.refinement.mapState bridge.sourceTarget) :=
  bridge.mappedExecution.run

/-- The mapped occurrence batch is current in the exact retained store view. -/
theorem mappedExecution_current
    (bridge : RevisionAlignedWave semanticAdmission operationalAdmission
      currentRevision) :
    CurrentBatch view batch := by
  have current := bridge.mappedExecution.current
  change CurrentBatch view
    (semanticAdmission.refinement.refinement.mapExecution
      bridge.sourceExecution).batch at current
  rw [bridge.mapsBatch] at current
  exact current

/-- The client observation of the concrete runtime target equals the source
execution observation.  This is the commuting square retained by NIK. -/
theorem clientObservation_commutes
    (bridge : RevisionAlignedWave semanticAdmission operationalAdmission
      currentRevision) :
    some (semantics.observe referenceTarget) =
      sourceObject.observe bridge.sourceExecution := by
  have agrees :=
    bridge.semanticActive.observationAgreement bridge.sourceExecution
  simpa only [runtimeObject, RevisionedExecution.observation,
    bridge.mapsTarget] using agrees

/-- Reactivate the same retained semantic cell and exact operational wave at
any revision with the same selected dependency values. -/
def activateAt
    (bridge : RevisionAlignedWave semanticAdmission operationalAdmission
      currentRevision)
    (current : dependencies.SameDependencies admittedRevision nextRevision) :
    RevisionAlignedWave semanticAdmission operationalAdmission nextRevision where
  semanticActive := semanticAdmission.activate current
  sourceStart := bridge.sourceStart
  sourceTarget := bridge.sourceTarget
  sourceExecution := bridge.sourceExecution
  mapsInitial := bridge.mapsInitial
  mapsTarget := bridge.mapsTarget
  mapsBatch := bridge.mapsBatch

/-- A relevant semantic dependency change blocks the joint bridge even when
the operational store and its payloads have not changed. -/
theorem noBridgeAfterRelevantSemanticChange
    (stale : Not
      (dependencies.SameDependencies admittedRevision nextRevision)) :
    Not (Nonempty
      (RevisionAlignedWave semanticAdmission operationalAdmission
        nextRevision)) := by
  rintro ⟨bridge⟩
  exact stale bridge.semanticActive.current

end RevisionAlignedWave

/-! ## Positive and adversarial controls -/

namespace Canary

open Mettapedia.GSLT.Dynamics.OperationalRevisionWaveAdmission.Canary

/-- An abstract source has one proof-relevant execution from the initial to
the target state. -/
inductive AbstractExecution : State -> State -> Type
  | reference : AbstractExecution initial target

/-- The source exposes only the same terminal-state observation used by the
runtime semantics. -/
def sourceObject : IndexedObservedOperationalObject StateView where
  operational :=
    { State := State
      Execution := AbstractExecution
      Meaning := visibleInvariant }
  observe := fun {_first last} _ => some (semantics.observe last)

def runtime : IndexedObservedOperationalObject StateView :=
  runtimeObject view0 semantics visibleInvariant

/-- The abstract execution is realized by the exact current occurrence batch
of the operational wave. -/
noncomputable def runtimeRefinement :
    IndexedObservedRefinement sourceObject runtime where
  refinement :=
    { mapState := id
      mapExecution := by
        intro first last execution
        cases execution
        exact RuntimeWave.referenceExecution admitted
      preservesMeaning := by
        intro state meaningful
        change visibleInvariant state at meaningful
        change visibleInvariant (id state)
        exact meaningful }
  commutes := by
    intro first last execution
    cases execution
    rfl

abbrev semanticDependencies : DependencySystem :=
  Mettapedia.GSLT.LanguageDef.NIKRouteAdmission.Canary.dependencySystem

noncomputable def semanticAdmission :
    IndexedObservedAdmittedAt semanticDependencies (false, false)
      sourceObject runtime :=
  ⟨runtimeRefinement⟩

abbrev BridgeAt (revision : semanticDependencies.Revision) :=
  RevisionAlignedWave semanticAdmission admitted revision

noncomputable def bridgeAtStoredRevision : BridgeAt (false, false) where
  semanticActive := semanticAdmission.activate
    (semanticDependencies.sameDependencies_refl (false, false))
  sourceStart := initial
  sourceTarget := target
  sourceExecution := .reference
  mapsInitial := rfl
  mapsTarget := rfl
  mapsBatch := rfl

/-- The second semantic revision coordinate is irrelevant to this artifact,
so the same exact runtime wave remains active there. -/
noncomputable def bridgeAtIrrelevantRevision : BridgeAt (false, true) :=
  bridgeAtStoredRevision.activateAt
    Mettapedia.GSLT.LanguageDef.NIKRouteAdmission.Canary.irrelevant_change_current

/-- Semantic reactivation preserves the exact batch, its runtime execution,
and the declared client observation. -/
theorem irrelevant_semantic_change_preserves_runtime_wave :
    bridgeAtIrrelevantRevision.mappedExecution.batch = batch /\
      semantics.run initial batch target /\
      some (semantics.observe target) =
        sourceObject.observe AbstractExecution.reference := by
  refine ⟨bridgeAtIrrelevantRevision.mappedExecution_batch,
    bridgeAtIrrelevantRevision.mappedExecution_runs, ?_⟩
  simpa [bridgeAtIrrelevantRevision, RevisionAlignedWave.activateAt,
    bridgeAtStoredRevision] using
      bridgeAtIrrelevantRevision.clientObservation_commutes

/-- The irrelevant transport is nonvacuous: its raw semantic revision really
changed. -/
theorem irrelevant_semantic_revision_is_distinct :
    (false, false) ≠ (false, true) := by
  decide

/-- Changing the selected semantic dependency blocks the bridge even though
the live runtime store and operational admission are unchanged. -/
theorem relevant_semantic_change_refuses_bridge :
    Not (Nonempty (BridgeAt (true, false))) :=
  RevisionAlignedWave.noBridgeAfterRelevantSemanticChange
    Mettapedia.GSLT.LanguageDef.NIKRouteAdmission.Canary.relevant_change_not_current

abbrev ReplayAt (newView : StoreView) :=
  OperationalAdmission Unit Unit newView completeContract semantics initial
    target demand 1 batch problem cost value geometry (1 / 2) visibleInvariant

/-- Keeping the identical payload while advancing the store revision cannot
replay the old occurrence identity. -/
theorem equal_payload_new_store_revision_refuses_wave :
    Not (Nonempty (ReplayAt (view0.replaceRevision 1 [()]))) :=
  RuntimeWave.noReplayAfterStoreRevisionChange admitted 1 [()] (by decide)

/-- One theorem-level discriminator for the two independent revision axes. -/
structure RevisionAxesSeparate : Prop where
  rawSemanticRevisionChanged : (false, false) ≠ (false, true)
  irrelevantSemanticChangeAdmitted : Nonempty (BridgeAt (false, true))
  relevantSemanticChangeRefused : Not (Nonempty (BridgeAt (true, false)))
  changedStoreRevisionRefused :
    Not (Nonempty (ReplayAt (view0.replaceRevision 1 [()])))
  observationStillCommutes :
    some (semantics.observe target) =
      sourceObject.observe AbstractExecution.reference

/-- Semantic dependency currentness and store occurrence currentness cannot
substitute for one another. -/
theorem semantic_and_store_revision_axes_are_separate :
    RevisionAxesSeparate where
  rawSemanticRevisionChanged := irrelevant_semantic_revision_is_distinct
  irrelevantSemanticChangeAdmitted := ⟨bridgeAtIrrelevantRevision⟩
  relevantSemanticChangeRefused := relevant_semantic_change_refuses_bridge
  changedStoreRevisionRefused := equal_payload_new_store_revision_refuses_wave
  observationStillCommutes :=
    irrelevant_semantic_change_preserves_runtime_wave.2.2

end Canary

/-! ## Axiom audit -/

#print axioms RuntimeWave.referenceExecution
#print axioms RuntimeWave.noCurrentBatchAfterStoreRevisionChange
#print axioms RuntimeWave.noReplayAfterStoreRevisionChange
#print axioms RevisionAlignedWave.mappedExecution_runs
#print axioms RevisionAlignedWave.mappedExecution_has_run
#print axioms RevisionAlignedWave.mappedExecution_current
#print axioms RevisionAlignedWave.clientObservation_commutes
#print axioms RevisionAlignedWave.noBridgeAfterRelevantSemanticChange
#print axioms Canary.irrelevant_semantic_change_preserves_runtime_wave
#print axioms Canary.relevant_semantic_change_refuses_bridge
#print axioms Canary.equal_payload_new_store_revision_refuses_wave
#print axioms Canary.semantic_and_store_revision_axes_are_separate

end Mettapedia.GSLT.LanguageDef.NIKOperationalRevisionBridge
