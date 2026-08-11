import Mettapedia.GSLT.Dynamics.ProofRelevantNeedNIK
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedOwnership
import Mettapedia.Languages.MeTTa.PrimeNeedReferenceSemantics

/-!
# Prime Need cache as an owned proof-relevant Need protocol

Prime's reference machine records an evaluator owner in every evaluating
cache.  This module identifies its cache-update primitives with the optional
owned Need protocol, rather than weakening Prime to the owner-free protocol.
Ownership may subsequently be erased through the separately proved
operational translation.

The results here concern the cell protocol: allocation, ownership, commit,
retry, cached observation, and origin inspection.  They do not claim that one
whole Prime machine instruction equals one cell event.  A machine instruction
may contain control-stack work, receipts, or both a commit and an observation;
the eventual physical adequacy theorem must lower it to a finite event trace.
-/

namespace Mettapedia.Languages.MeTTa.PrimeNeedProtocolBridge


open Mettapedia.GSLT.Dynamics
universe uOrigin uValue uStableFault uRetryableFault

/-- Exact decomposition of Prime's three outcome classes. -/
def outcomeAlgebra
    (Value : Type uValue) (StableFault : Type uStableFault)
    (RetryableFault : Type uRetryableFault) :
    ProofRelevantNeed.OutcomeAlgebra
      (PrimeNeedReference.Produced Value StableFault RetryableFault) where
  Value := Value
  StableFault := StableFault
  RetryableFault := PrimeNeedReference.RetryReason RetryableFault
  encode
    | .value value => .value value
    | .stableFault fault => .stableFault fault
    | .retryableFault reason => .retryableFault reason
  decode
    | .value value => .value value
    | .stableFault fault => .stableFault fault
    | .retryableFault reason => .retryableFault reason
  decode_encode := by intro outcome; cases outcome <;> rfl
  encode_decode := by intro outcome; cases outcome <;> rfl

/-- Prime's cache is definitionally the owned protocol state once its
immutable record origin is restored. -/
def recordState {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (record : PrimeNeedReference.CellRecord Origin Value StableFault) :
    ProofRelevantNeed.Ownership.CellState PrimeNeedReference.EvaluatorId Origin Value StableFault :=
  match record.cache with
  | .suspended => .suspended record.origin
  | .evaluating owner => .evaluating record.origin owner
  | .value value => .cachedValue record.origin value
  | .stableFault fault => .cachedStableFault record.origin fault

/-- Observe one cell of a Prime heap as one owned protocol state. -/
def heapState {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault) (cell : PrimeNeedReference.CellId) :
    ProofRelevantNeed.Ownership.CellState PrimeNeedReference.EvaluatorId Origin Value StableFault :=
  match heap.lookup cell with
  | none => .absent
  | some record => recordState record

@[simp] theorem heapState_empty
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} (cell : PrimeNeedReference.CellId) :
    heapState (PrimeNeedReference.Heap.empty : PrimeNeedReference.Heap Origin Value StableFault) cell =
      .absent :=
  rfl

/-- Successful Prime allocation is exactly an owned Need allocation event. -/
def allocate_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    {heap next : PrimeNeedReference.Heap Origin Value StableFault}
    {cell : PrimeNeedReference.CellId} {origin : Origin}
    (allocated : heap.allocate? cell origin = some next) :
    ProofRelevantNeed.Ownership.Step
      (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell) (.allocate cell origin) (heapState next cell) := by
  have absent : heap.lookup cell = none := by
    unfold PrimeNeedReference.Heap.allocate? at allocated
    split at allocated
    · contradiction
    · assumption
  have present := PrimeNeedReference.Heap.allocate?_lookup_same allocated
  simpa [heapState, absent, present, recordState] using
    (ProofRelevantNeed.Ownership.Step.allocate
      (RetryableFault := PrimeNeedReference.RetryReason RetryableFault)
      (cell := cell) origin)

/-- Claiming a suspended Prime cache with a fresh evaluator is exactly the
owned begin-evaluation event. -/
def beginEvaluation_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault) (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault)
    (owner : PrimeNeedReference.EvaluatorId)
    (present : heap.lookup cell = some record)
    (suspended : record.cache = .suspended) :
    ProofRelevantNeed.Ownership.Step (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell)
      (.beginEvaluation cell record.origin owner)
      (heapState (heap.setKnownCache cell record (.evaluating owner)) cell) := by
  simpa [heapState, present, suspended, recordState] using
    (ProofRelevantNeed.Ownership.Step.beginEvaluation
      (RetryableFault := PrimeNeedReference.RetryReason RetryableFault)
      (cell := cell) record.origin owner)

/-- A successful owner-matched value commit is the exact owned commit event. -/
def commitValue_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault) (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault)
    (owner : PrimeNeedReference.EvaluatorId) (value : Value)
    (present : heap.lookup cell = some record)
    (owned : record.cache = .evaluating owner) :
    ProofRelevantNeed.Ownership.Step (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell)
      (.commitValue cell record.origin owner value)
      (heapState (heap.setKnownCache cell record (.value value)) cell) := by
  simpa [heapState, present, owned, recordState] using
    (ProofRelevantNeed.Ownership.Step.commitValue
      (RetryableFault := PrimeNeedReference.RetryReason RetryableFault)
      (cell := cell) record.origin owner value)

/-- Stable faults are cached by the same owner-matched protocol. -/
def commitStableFault_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault) (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault)
    (owner : PrimeNeedReference.EvaluatorId) (fault : StableFault)
    (present : heap.lookup cell = some record)
    (owned : record.cache = .evaluating owner) :
    ProofRelevantNeed.Ownership.Step (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell)
      (.commitStableFault cell record.origin owner fault)
      (heapState (heap.setKnownCache cell record (.stableFault fault)) cell) := by
  simpa [heapState, present, owned, recordState] using
    (ProofRelevantNeed.Ownership.Step.commitStableFault
      (RetryableFault := PrimeNeedReference.RetryReason RetryableFault)
      (cell := cell) record.origin owner fault)

/-- Retryable faults reopen the same origin and remain uncached. -/
def retry_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault) (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault)
    (owner : PrimeNeedReference.EvaluatorId) (reason : PrimeNeedReference.RetryReason RetryableFault)
    (present : heap.lookup cell = some record)
    (owned : record.cache = .evaluating owner) :
    ProofRelevantNeed.Ownership.Step (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell) (.retry cell record.origin owner reason)
      (heapState (heap.setKnownCache cell record .suspended) cell) := by
  simpa [heapState, present, owned, recordState] using
    (ProofRelevantNeed.Ownership.Step.retry (cell := cell) record.origin owner reason)

/-- A cached Prime value demand observes without reopening evaluation. -/
def observeValue_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault) (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault) (value : Value)
    (present : heap.lookup cell = some record)
    (cached : record.cache = .value value) :
    ProofRelevantNeed.Ownership.Step (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell) (.observeValue cell record.origin value)
      (heapState heap cell) := by
  simpa [heapState, present, cached, recordState] using
    (ProofRelevantNeed.Ownership.Step.observeValue
      (RetryableFault := PrimeNeedReference.RetryReason RetryableFault)
      (cell := cell) record.origin value)

/-- Stable-fault demand is likewise a cached observation. -/
def observeStableFault_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault) (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault) (fault : StableFault)
    (present : heap.lookup cell = some record)
    (cached : record.cache = .stableFault fault) :
    ProofRelevantNeed.Ownership.Step (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell) (.observeStableFault cell record.origin fault)
      (heapState heap cell) := by
  simpa [heapState, present, cached, recordState] using
    (ProofRelevantNeed.Ownership.Step.observeStableFault
      (RetryableFault := PrimeNeedReference.RetryReason RetryableFault)
      (cell := cell) record.origin fault)

/-- Origin inspection is available in every allocated cache state and never
changes ownership or the cached outcome. -/
theorem inspectOrigin_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault) (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault)
    (present : heap.lookup cell = some record) :
    Nonempty
      (ProofRelevantNeed.Ownership.Step (PrimeNeedReference.RetryReason RetryableFault) cell
        (heapState heap cell) (.inspectOrigin cell record.origin)
        (heapState heap cell)) := by
  cases cacheEquation : record.cache with
  | suspended =>
      exact ⟨by simpa [heapState, present, cacheEquation, recordState] using
        (ProofRelevantNeed.Ownership.Step.inspectSuspended
          (RetryableFault := PrimeNeedReference.RetryReason RetryableFault)
          (cell := cell) record.origin)⟩
  | evaluating owner =>
      exact ⟨by simpa [heapState, present, cacheEquation, recordState] using
        (ProofRelevantNeed.Ownership.Step.inspectEvaluating
          (RetryableFault := PrimeNeedReference.RetryReason RetryableFault)
          (cell := cell) record.origin owner)⟩
  | value value =>
      exact ⟨by simpa [heapState, present, cacheEquation, recordState] using
        (ProofRelevantNeed.Ownership.Step.inspectValue
          (RetryableFault := PrimeNeedReference.RetryReason RetryableFault)
          (cell := cell) record.origin value)⟩
  | stableFault fault =>
      exact ⟨by simpa [heapState, present, cacheEquation, recordState] using
        (ProofRelevantNeed.Ownership.Step.inspectStableFault
          (RetryableFault := PrimeNeedReference.RetryReason RetryableFault)
          (cell := cell) record.origin fault)⟩

/-! ## Finite event batches for one machine instruction -/

/-- Allocation contributes one exact cell event to a machine instruction. -/
def allocateBatch_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    {heap next : PrimeNeedReference.Heap Origin Value StableFault}
    {cell : PrimeNeedReference.CellId} {origin : Origin}
    (allocated : heap.allocate? cell origin = some next) :
    ProofRelevantNeed.Ownership.Trace
      (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell) (heapState next cell) :=
  ProofRelevantNeed.Ownership.Trace.singleton (.allocate cell origin)
    (allocate_projects (RetryableFault := RetryableFault) allocated)

/-- Claiming a suspended cache contributes one owner-bearing event. -/
def beginEvaluationBatch_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault)
    (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault)
    (owner : PrimeNeedReference.EvaluatorId)
    (present : heap.lookup cell = some record)
    (suspended : record.cache = .suspended) :
    ProofRelevantNeed.Ownership.Trace
      (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell)
      (heapState (heap.setKnownCache cell record (.evaluating owner)) cell) :=
  ProofRelevantNeed.Ownership.Trace.singleton
    (.beginEvaluation cell record.origin owner)
    (beginEvaluation_projects heap cell record owner present suspended)

/-- A successful returning instruction commits and then observes.  These are
two semantic events even though the second is a cache-state self-loop. -/
def commitValueObserveBatch_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault)
    (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault)
    (owner : PrimeNeedReference.EvaluatorId) (value : Value)
    (present : heap.lookup cell = some record)
    (owned : record.cache = .evaluating owner) :
    ProofRelevantNeed.Ownership.Trace
      (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell)
      (heapState (heap.setKnownCache cell record (.value value)) cell) := by
  let updated := heap.setKnownCache cell record (.value value)
  let updatedRecord : PrimeNeedReference.CellRecord Origin Value StableFault :=
    { record with cache := .value value }
  have commit := commitValue_projects (RetryableFault := RetryableFault)
    heap cell record owner value present owned
  have updatedPresent : updated.lookup cell = some updatedRecord := by
    simp [updated, updatedRecord]
  have observe := observeValue_projects (RetryableFault := RetryableFault)
    updated cell updatedRecord value updatedPresent rfl
  exact .tail (.commitValue cell record.origin owner value) commit
    (.tail (.observeValue cell record.origin value) observe (.refl _))

/-- Stable-fault return has the same two-event commit/observe shape. -/
def commitStableFaultObserveBatch_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault)
    (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault)
    (owner : PrimeNeedReference.EvaluatorId) (fault : StableFault)
    (present : heap.lookup cell = some record)
    (owned : record.cache = .evaluating owner) :
    ProofRelevantNeed.Ownership.Trace
      (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell)
      (heapState (heap.setKnownCache cell record (.stableFault fault)) cell) := by
  let updated := heap.setKnownCache cell record (.stableFault fault)
  let updatedRecord : PrimeNeedReference.CellRecord Origin Value StableFault :=
    { record with cache := .stableFault fault }
  have commit := commitStableFault_projects (RetryableFault := RetryableFault)
    heap cell record owner fault present owned
  have updatedPresent : updated.lookup cell = some updatedRecord := by
    simp [updated, updatedRecord]
  have observe := observeStableFault_projects
    (RetryableFault := RetryableFault) updated cell updatedRecord fault
    updatedPresent rfl
  exact .tail (.commitStableFault cell record.origin owner fault) commit
    (.tail (.observeStableFault cell record.origin fault) observe (.refl _))

/-- Retryable return reopens the suspension and is not followed by an outcome
observation. -/
def retryBatch_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault)
    (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault)
    (owner : PrimeNeedReference.EvaluatorId)
    (reason : PrimeNeedReference.RetryReason RetryableFault)
    (present : heap.lookup cell = some record)
    (owned : record.cache = .evaluating owner) :
    ProofRelevantNeed.Ownership.Trace
      (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell)
      (heapState (heap.setKnownCache cell record .suspended) cell) :=
  ProofRelevantNeed.Ownership.Trace.singleton
    (.retry cell record.origin owner reason)
    (retry_projects heap cell record owner reason present owned)

/-- Cached value demand contributes observation but no evaluation event. -/
def observeValueBatch_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault)
    (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault)
    (value : Value) (present : heap.lookup cell = some record)
    (cached : record.cache = .value value) :
    ProofRelevantNeed.Ownership.Trace
      (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell) (heapState heap cell) :=
  ProofRelevantNeed.Ownership.Trace.singleton
    (.observeValue cell record.origin value)
    (observeValue_projects heap cell record value present cached)

/-- Cached stable-fault demand also contributes one observation event. -/
def observeStableFaultBatch_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault)
    (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault)
    (fault : StableFault) (present : heap.lookup cell = some record)
    (cached : record.cache = .stableFault fault) :
    ProofRelevantNeed.Ownership.Trace
      (PrimeNeedReference.RetryReason RetryableFault) cell
      (heapState heap cell) (heapState heap cell) :=
  ProofRelevantNeed.Ownership.Trace.singleton
    (.observeStableFault cell record.origin fault)
    (observeStableFault_projects heap cell record fault present cached)

/-- Origin inspection is a one-event batch for every allocated state. -/
theorem inspectOriginBatch_projects
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (heap : PrimeNeedReference.Heap Origin Value StableFault)
    (cell : PrimeNeedReference.CellId)
    (record : PrimeNeedReference.CellRecord Origin Value StableFault)
    (present : heap.lookup cell = some record) :
    Nonempty
      (ProofRelevantNeed.Ownership.Trace
        (PrimeNeedReference.RetryReason RetryableFault) cell
        (heapState heap cell) (heapState heap cell)) := by
  obtain ⟨inspection⟩ := inspectOrigin_projects
    (RetryableFault := RetryableFault) heap cell record present
  exact ⟨ProofRelevantNeed.Ownership.Trace.singleton
    (.inspectOrigin cell record.origin) inspection⟩

namespace BatchCanary

def commitThenObserve :
    ProofRelevantNeed.Ownership.Trace
      (Cell := Nat) (Owner := Bool) (Origin := Nat) (Value := Nat)
      (StableFault := Nat) Nat 0 (.evaluating 7 true)
      (.cachedValue 7 11) :=
  .tail (.commitValue 0 7 true 11) (.commitValue 7 true 11)
    (.tail (.observeValue 0 7 11) (.observeValue 7 11)
      (.refl (.cachedValue 7 11)))

theorem commitThenObserve_events :
    commitThenObserve.events =
      [ .commitValue 0 7 true 11, .observeValue 0 7 11 ] :=
  rfl

/-- Negative canary: endpoint equality cannot collapse the observation event
out of the instruction batch. -/
theorem commitThenObserve_is_not_one_event :
    commitThenObserve.events ≠ [.commitValue 0 7 true 11] := by
  simp [commitThenObserve_events]

end BatchCanary

/-- A mismatched owner cannot be laundered into a successful cache commit. -/
theorem wrongOwner_cannot_commit
    {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}
    (cell : PrimeNeedReference.CellId) (origin : Origin)
    (expected actual : PrimeNeedReference.EvaluatorId)
    (value : Value) (different : expected ≠ actual) :
    IsEmpty
      (ProofRelevantNeed.Ownership.Step
        (Cell := PrimeNeedReference.CellId)
        (Owner := PrimeNeedReference.EvaluatorId) (Origin := Origin)
        (Value := Value) (StableFault := StableFault)
        (PrimeNeedReference.RetryReason RetryableFault) cell
        (.evaluating origin expected)
        (.commitValue cell origin actual value) (.cachedValue origin value)) := by
  constructor
  intro impossible
  cases impossible
  exact different rfl

end Mettapedia.Languages.MeTTa.PrimeNeedProtocolBridge
