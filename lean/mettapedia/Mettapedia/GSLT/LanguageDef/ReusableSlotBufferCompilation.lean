import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation

/-!
# Certified reuse of finite scratch-slot buffers

A generated rule machine commonly has a finite dense slot inventory for each
transaction.  The source implementation may allocate a fresh empty buffer for
every transaction.  When completed buffers cross the transaction boundary by
value, a backend can instead clear one buffer and retain its capacity.

This module isolates the required reset law.  Source execution allocates a
fresh logical buffer per transaction.  Compiled execution threads one physical
buffer, resets every slot before the next transaction, and publishes the same
ordered snapshots.  Omitting the reset is exhibited as a negative canary.
-/

namespace Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation

universe uValue

/-- A finite dense scratch buffer. -/
abbrev Buffer (width : Nat) (Value : Type uValue) :=
  Fin width -> Option Value

/-- One transaction writes a finite sequence of dense slots. -/
abbrev Transaction (width : Nat) (Value : Type uValue) :=
  List (Fin width × Value)

def emptyBuffer : Buffer width Value := fun _ => none

def write [DecidableEq (Fin width)]
    (buffer : Buffer width Value) (entry : Fin width × Value) :
    Buffer width Value :=
  fun slot => if slot = entry.1 then some entry.2 else buffer slot

def runFrom [DecidableEq (Fin width)] :
    Buffer width Value -> Transaction width Value -> Buffer width Value
  | buffer, [] => buffer
  | buffer, entry :: entries => runFrom (write buffer entry) entries

def runFresh [DecidableEq (Fin width)]
    (transaction : Transaction width Value) : Buffer width Value :=
  runFrom emptyBuffer transaction

/-- Clearing restores the abstract empty state while a realization may retain
the physical allocation and its capacity. -/
def reset (_buffer : Buffer width Value) : Buffer width Value :=
  emptyBuffer

/-- Reify a buffer so transaction results cross the scratch-region boundary
as complete values rather than references into the reusable storage. -/
def snapshot (buffer : Buffer width Value) : List (Option Value) :=
  List.ofFn buffer

/-- Source semantics: each transaction starts with a fresh allocation. -/
def executeFresh [DecidableEq (Fin width)]
    (transactions : List (Transaction width Value)) :
    List (List (Option Value)) :=
  transactions.map fun transaction => snapshot (runFresh transaction)

/-- Compiled semantics: one physical buffer is reset and reused. -/
def executeReusableFrom [DecidableEq (Fin width)] :
    List (Transaction width Value) -> Buffer width Value ->
      List (List (Option Value))
  | [], _ => []
  | transaction :: transactions, buffer =>
      let completed := runFrom (reset buffer) transaction
      snapshot completed :: executeReusableFrom transactions completed

def executeReusable [DecidableEq (Fin width)]
    (transactions : List (Transaction width Value)) :
    List (List (Option Value)) :=
  executeReusableFrom transactions emptyBuffer

/-- Reset-and-reuse preserves every ordered transaction snapshot. -/
theorem executeReusableFrom_eq_fresh [DecidableEq (Fin width)]
    (transactions : List (Transaction width Value))
    (buffer : Buffer width Value) :
    executeReusableFrom transactions buffer = executeFresh transactions := by
  induction transactions generalizing buffer with
  | nil => rfl
  | cons transaction transactions inductionHypothesis =>
      simp [executeReusableFrom, executeFresh, reset, runFresh,
        inductionHypothesis]

theorem executeReusable_eq_fresh [DecidableEq (Fin width)]
    (transactions : List (Transaction width Value)) :
    executeReusable transactions = executeFresh transactions := by
  exact executeReusableFrom_eq_fresh transactions emptyBuffer

/-- A busy shared lease may fall back to fresh execution without changing the
observation.  This licenses nonblocking `tryAcquire` implementations. -/
def executeOpportunistic [DecidableEq (Fin width)]
    (leaseAvailable : Bool)
    (transactions : List (Transaction width Value)) :
    List (List (Option Value)) :=
  if leaseAvailable then executeReusable transactions
  else executeFresh transactions

theorem executeOpportunistic_eq_fresh [DecidableEq (Fin width)]
    (leaseAvailable : Bool)
    (transactions : List (Transaction width Value)) :
    executeOpportunistic leaseAvailable transactions =
      executeFresh transactions := by
  cases leaseAvailable <;>
    simp [executeOpportunistic, executeReusable_eq_fresh]

/-- Authored transaction batch before lifetime lowering. -/
structure FreshSlotProgram (width : Nat) (Value : Type uValue) where
  transactions : List (Transaction width Value)

/-- Generated artifact whose transactions share one resettable slot buffer. -/
structure ReusableSlotProgram (width : Nat) (Value : Type uValue) where
  transactions : List (Transaction width Value)

def compile (source : FreshSlotProgram width Value) :
    ReusableSlotProgram width Value :=
  { transactions := source.transactions }

/-- Reusable scratch-slot lowering as a composable certified realization. -/
def reusableSlotBufferRealization [DecidableEq (Fin width)] :
    Mettapedia.GSLT.SimpleRealization
      (FreshSlotProgram width Value)
      (ReusableSlotProgram width Value)
      (List (List (Option Value))) where
  compile := fun _ source => compile source
  observeSource := fun _ source => executeFresh source.transactions
  observeArtifact := fun _ artifact =>
    executeReusable artifact.transactions
  adequate := by
    intro _ source
    exact executeReusable_eq_fresh source.transactions

/-! ## Allocation-cost certificate -/

/-- Fresh execution allocates one physical slot buffer per transaction. -/
def freshAllocationCount (transactions : List (Transaction width Value)) : Nat :=
  transactions.length

/-- Reusable execution needs at most one physical buffer. -/
def reusableAllocationCount
    (transactions : List (Transaction width Value)) : Nat :=
  if transactions.isEmpty then 0 else 1

theorem reusableAllocationCount_le_fresh
    (transactions : List (Transaction width Value)) :
    reusableAllocationCount transactions <= freshAllocationCount transactions := by
  cases transactions <;> simp [reusableAllocationCount, freshAllocationCount]

theorem reusableAllocationCount_lt_fresh_of_two_le
    (transactions : List (Transaction width Value))
    (multiple : 2 <= transactions.length) :
    reusableAllocationCount transactions < freshAllocationCount transactions := by
  cases transactions with
  | nil => simp at multiple
  | cons transaction transactions =>
      simp at multiple
      have positive : 0 < transactions.length := by omega
      simpa [reusableAllocationCount, freshAllocationCount] using positive

/-! ## Property-directed admission at a call boundary -/

/-- Lifetime facts supplied by the generated storage/effect plan. -/
inductive ScratchLifetime where
  | callLocal
  | retained
  deriving DecidableEq, Repr

/-- How the authored observation crosses the call boundary.  A reference may
point into scratch storage, whereas a value is complete in its new owner. -/
inductive BoundaryPayload where
  | value
  | reference
  deriving DecidableEq, Repr

/-- The complete local property needed to reuse physical scratch. -/
structure ReusePlan where
  lifetime : ScratchLifetime
  boundary : BoundaryPayload
  deriving DecidableEq, Repr

def ReusePlan.supportsReuse : ReusePlan → Bool
  | ⟨.callLocal, .value⟩ => true
  | _ => false

def reusableCallPlan : ReusePlan where
  lifetime := .callLocal
  boundary := .value

/-- A batch of calls whose public result is computed from the complete value
snapshot of each call. -/
structure ObservableProgram
    (width : Nat) (Value : Type uValue) (Observation : Type*) where
  transactions : List (Transaction width Value)
  observe : List (Option Value) → Observation

/-- Generated realization retaining the same observer and transaction order,
but sharing one resettable physical buffer. -/
structure ReusableObservableProgram
    (width : Nat) (Value : Type uValue) (Observation : Type*) where
  transactions : List (Transaction width Value)
  observe : List (Option Value) → Observation

def compileObservable
    (source : ObservableProgram width Value Observation) :
    ReusableObservableProgram width Value Observation :=
  { transactions := source.transactions, observe := source.observe }

def observeFreshCalls [DecidableEq (Fin width)]
    (source : ObservableProgram width Value Observation) :
    List Observation :=
  (executeFresh source.transactions).map source.observe

def observeReusableCalls [DecidableEq (Fin width)]
    (artifact : ReusableObservableProgram width Value Observation) :
    List Observation :=
  (executeReusable artifact.transactions).map artifact.observe

/-- Value observations cannot distinguish a fresh buffer from a correctly
reset reusable buffer. -/
theorem observeReusableCalls_compileObservable
    [DecidableEq (Fin width)]
    (source : ObservableProgram width Value Observation) :
    observeReusableCalls (compileObservable source) =
      observeFreshCalls source := by
  simp only [observeReusableCalls, compileObservable, observeFreshCalls]
  rw [executeReusable_eq_fresh]

/-- The generated lifetime/effect recognizer fails closed unless scratch is
call-local and every result crosses the boundary by value. -/
def compileObservable?
    (plan : ReusePlan)
    (source : ObservableProgram width Value Observation) :
    Option (ReusableObservableProgram width Value Observation) :=
  if plan.supportsReuse then some (compileObservable source) else none

theorem compileObservable?_exact [DecidableEq (Fin width)]
    (plan : ReusePlan)
    (source : ObservableProgram width Value Observation)
    (artifact : ReusableObservableProgram width Value Observation)
    (accepted : compileObservable? plan source = some artifact) :
    observeReusableCalls artifact = observeFreshCalls source := by
  unfold compileObservable? at accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst artifact
    exact observeReusableCalls_compileObservable source
  · simp at accepted

theorem compileObservable?_allocationCount_le
    (plan : ReusePlan)
    (source : ObservableProgram width Value Observation)
    (artifact : ReusableObservableProgram width Value Observation)
    (accepted : compileObservable? plan source = some artifact) :
    reusableAllocationCount artifact.transactions ≤
      freshAllocationCount source.transactions := by
  unfold compileObservable? at accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst artifact
    exact reusableAllocationCount_le_fresh source.transactions
  · simp at accepted

/-! ## Variable-length sequence workspaces -/

/-- Physical sequence state separates the visible prefix from retained
capacity.  Reset removes every logical element without shrinking storage. -/
structure SequenceBuffer (Value : Type uValue) where
  logical : List Value
  capacity : Nat
  valid : logical.length ≤ capacity

def emptySequenceBuffer : SequenceBuffer Value where
  logical := []
  capacity := 0
  valid := by simp

def resetSequenceBuffer (buffer : SequenceBuffer Value) :
    SequenceBuffer Value where
  logical := []
  capacity := buffer.capacity
  valid := by simp

def fillSequenceBuffer (buffer : SequenceBuffer Value)
    (values : List Value) : SequenceBuffer Value where
  logical := values
  capacity := max buffer.capacity values.length
  valid := Nat.le_max_right _ _

/-- Execute calls through one physical sequence buffer.  The completed value
is copied into the observation list before the logical buffer is reset. -/
def executeSequenceCallsFrom :
    List (List Value) → SequenceBuffer Value →
      List (List Value) × SequenceBuffer Value
  | [], buffer => ([], buffer)
  | values :: calls, buffer =>
      let completed := fillSequenceBuffer (resetSequenceBuffer buffer) values
      let tail := executeSequenceCallsFrom calls
        (resetSequenceBuffer completed)
      (completed.logical :: tail.1, tail.2)

def executeSequenceCalls (calls : List (List Value)) :
    List (List Value) × SequenceBuffer Value :=
  executeSequenceCallsFrom calls emptySequenceBuffer

/-- Reuse preserves every ordered sequence exactly, including empty calls. -/
theorem executeSequenceCallsFrom_observations
    (calls : List (List Value)) (buffer : SequenceBuffer Value) :
    (executeSequenceCallsFrom calls buffer).1 = calls := by
  induction calls generalizing buffer with
  | nil => rfl
  | cons values calls inductionHypothesis =>
      simp [executeSequenceCallsFrom, fillSequenceBuffer,
        resetSequenceBuffer, inductionHypothesis]

theorem executeSequenceCalls_observations
    (calls : List (List Value)) :
    (executeSequenceCalls calls).1 = calls := by
  exact executeSequenceCallsFrom_observations calls emptySequenceBuffer

/-- Reuse never reduces retained capacity while calls are being threaded. -/
theorem executeSequenceCallsFrom_capacity_mono
    (calls : List (List Value)) (buffer : SequenceBuffer Value) :
    buffer.capacity ≤ (executeSequenceCallsFrom calls buffer).2.capacity := by
  induction calls generalizing buffer with
  | nil => simp [executeSequenceCallsFrom]
  | cons values calls inductionHypothesis =>
      have tail := inductionHypothesis
        (resetSequenceBuffer
          (fillSequenceBuffer (resetSequenceBuffer buffer) values))
      simp only [resetSequenceBuffer, fillSequenceBuffer] at tail
      simp only [executeSequenceCallsFrom]
      exact Nat.le_trans
        (Nat.le_max_left buffer.capacity values.length) tail

structure SequenceObservableProgram
    (Value : Type uValue) (Observation : Type*) where
  calls : List (List Value)
  observe : List Value → Observation

structure ReusableSequenceObservableProgram
    (Value : Type uValue) (Observation : Type*) where
  calls : List (List Value)
  observe : List Value → Observation

def compileSequenceObservable
    (source : SequenceObservableProgram Value Observation) :
    ReusableSequenceObservableProgram Value Observation :=
  { calls := source.calls, observe := source.observe }

def observeFreshSequences
    (source : SequenceObservableProgram Value Observation) :
    List Observation := source.calls.map source.observe

def observeReusableSequences
    (artifact : ReusableSequenceObservableProgram Value Observation) :
    List Observation :=
  (executeSequenceCalls artifact.calls).1.map artifact.observe

theorem observeReusableSequences_compile
    (source : SequenceObservableProgram Value Observation) :
    observeReusableSequences (compileSequenceObservable source) =
      observeFreshSequences source := by
  simp [observeReusableSequences, compileSequenceObservable,
    observeFreshSequences, executeSequenceCalls_observations]

def compileSequenceObservable?
    (plan : ReusePlan)
    (source : SequenceObservableProgram Value Observation) :
    Option (ReusableSequenceObservableProgram Value Observation) :=
  if plan.supportsReuse then some (compileSequenceObservable source) else none

theorem compileSequenceObservable?_exact
    (plan : ReusePlan)
    (source : SequenceObservableProgram Value Observation)
    (artifact : ReusableSequenceObservableProgram Value Observation)
    (accepted : compileSequenceObservable? plan source = some artifact) :
    observeReusableSequences artifact = observeFreshSequences source := by
  unfold compileSequenceObservable? at accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst artifact
    exact observeReusableSequences_compile source
  · simp at accepted

def freshSequenceAllocationCount
    (calls : List (List Value)) : Nat := calls.length

def reusableSequenceAllocationCount
    (calls : List (List Value)) : Nat := if calls.isEmpty then 0 else 1

theorem reusableSequenceAllocationCount_le_fresh
    (calls : List (List Value)) :
    reusableSequenceAllocationCount calls ≤
      freshSequenceAllocationCount calls := by
  cases calls <;>
    simp [reusableSequenceAllocationCount, freshSequenceAllocationCount]

theorem compileSequenceObservable?_allocationCount_le
    (plan : ReusePlan)
    (source : SequenceObservableProgram Value Observation)
    (artifact : ReusableSequenceObservableProgram Value Observation)
    (accepted : compileSequenceObservable? plan source = some artifact) :
    reusableSequenceAllocationCount artifact.calls ≤
      freshSequenceAllocationCount source.calls := by
  unfold compileSequenceObservable? at accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst artifact
    exact reusableSequenceAllocationCount_le_fresh source.calls
  · simp at accepted

/-! ## Resettable call-local regions -/

/-- One call populates an append-only logical region and publishes only a
complete observation.  The observer cannot retain a reference to the physical
buffer because that buffer is absent from its type. -/
structure RegionCall (Value : Type uValue) (Observation : Type*) where
  values : List Value
  publish : List Value → Observation

def observeFreshRegionCalls
    (calls : List (RegionCall Value Observation)) : List Observation :=
  calls.map fun call => call.publish call.values

/-- Compiled execution resets one region, fills it, publishes a value, and
then threads only the retained capacity into the next call. -/
def observeReusableRegionCallsFrom :
    List (RegionCall Value Observation) → SequenceBuffer Value →
      List Observation × SequenceBuffer Value
  | [], buffer => ([], buffer)
  | call :: calls, buffer =>
      let completed := fillSequenceBuffer (resetSequenceBuffer buffer)
        call.values
      let tail := observeReusableRegionCallsFrom calls
        (resetSequenceBuffer completed)
      (call.publish completed.logical :: tail.1, tail.2)

def observeReusableRegionCalls
    (calls : List (RegionCall Value Observation)) :
    List Observation × SequenceBuffer Value :=
  observeReusableRegionCallsFrom calls emptySequenceBuffer

/-- A resettable retained arena is observationally exact when only a complete
value crosses each call boundary. -/
theorem observeReusableRegionCallsFrom_exact
    (calls : List (RegionCall Value Observation))
    (buffer : SequenceBuffer Value) :
    (observeReusableRegionCallsFrom calls buffer).1 =
      observeFreshRegionCalls calls := by
  induction calls generalizing buffer with
  | nil => rfl
  | cons call calls inductionHypothesis =>
      simp [observeReusableRegionCallsFrom, observeFreshRegionCalls,
        fillSequenceBuffer, resetSequenceBuffer, inductionHypothesis]

theorem observeReusableRegionCalls_exact
    (calls : List (RegionCall Value Observation)) :
    (observeReusableRegionCalls calls).1 = observeFreshRegionCalls calls := by
  exact observeReusableRegionCallsFrom_exact calls emptySequenceBuffer

/-- Retaining a call-local region never adds a call-sized allocation relative
to allocating a fresh region for every call. -/
theorem reusableRegionAllocationCount_le_fresh
    (calls : List (RegionCall Value Observation)) :
    reusableSequenceAllocationCount (calls.map (·.values)) ≤ calls.length := by
  simpa [freshSequenceAllocationCount] using
    (reusableSequenceAllocationCount_le_fresh (calls.map (·.values)))

/-- A call either publishes a complete value or fails after allocating an
unobservable partial region. -/
inductive RegionAttempt (Value : Type uValue) (Observation : Type*) where
  | success (values : List Value) (publish : List Value → Observation)
  | failure (allocated : List Value)

def observeFreshRegionAttempt :
    RegionAttempt Value Observation → Option Observation
  | .success values publish => some (publish values)
  | .failure _ => none

def executeReusableRegionAttempt
    (attempt : RegionAttempt Value Observation)
    (buffer : SequenceBuffer Value) :
    Option Observation × SequenceBuffer Value :=
  match attempt with
  | .success values publish =>
      let completed := fillSequenceBuffer (resetSequenceBuffer buffer) values
      (some (publish completed.logical), resetSequenceBuffer completed)
  | .failure allocated =>
      let completed := fillSequenceBuffer (resetSequenceBuffer buffer) allocated
      (none, resetSequenceBuffer completed)

def executeReusableRegionAttemptsFrom :
    List (RegionAttempt Value Observation) → SequenceBuffer Value →
      List (Option Observation) × SequenceBuffer Value
  | [], buffer => ([], buffer)
  | attempt :: attempts, buffer =>
      let completed := executeReusableRegionAttempt attempt buffer
      let tail := executeReusableRegionAttemptsFrom attempts completed.2
      (completed.1 :: tail.1, tail.2)

/-- Allocation failure publishes no semantic result, and resetting its
private watermark prevents partial objects from affecting later calls. -/
theorem executeReusableRegionAttemptsFrom_exact
    (attempts : List (RegionAttempt Value Observation))
    (buffer : SequenceBuffer Value) :
    (executeReusableRegionAttemptsFrom attempts buffer).1 =
      attempts.map observeFreshRegionAttempt := by
  induction attempts generalizing buffer with
  | nil => rfl
  | cons attempt attempts inductionHypothesis =>
      cases attempt <;>
        simp [executeReusableRegionAttemptsFrom,
          executeReusableRegionAttempt, observeFreshRegionAttempt,
          fillSequenceBuffer, resetSequenceBuffer, inductionHypothesis]

/-! ## Exact generated call-plan admission -/

/-- The two field forms accepted by the storage-plan wire decoder. -/
inductive CallPlanField where
  | symbol (value : String)
  | natural (value : Nat)
  deriving DecidableEq, Repr

/-- The eight payload fields of `proof-call-region-plan-v1`.  Operation,
action, and machine remain data so the same decoder serves every guest. -/
structure GeneratedCallPlan where
  operation : String
  actionIndex : Nat
  machine : String
  owner : String
  provable : String
  region : String
  layout : String
  observation : String
  deriving DecidableEq, Repr

/-- Decode exactly one generated call-plan payload, rejecting every other
arity or field kind. -/
def decodeGeneratedCallPlan : List CallPlanField → Option GeneratedCallPlan
  | [.symbol operation, .natural actionIndex, .symbol machine,
      .symbol owner, .symbol provable, .symbol region, .symbol layout,
      .symbol observation] =>
      some {
        operation := operation
        actionIndex := actionIndex
        machine := machine
        owner := owner
        provable := provable
        region := region
        layout := layout
        observation := observation }
  | _ => none

/-- The six payload fields of `proof-workspace-plan-v1`.  The carrier names a
closed generic physical realization rather than reusing the guest sequence
layout as a proxy for scratch representation. -/
structure GeneratedWorkspacePlan where
  operation : String
  actionIndex : Nat
  machine : String
  carrier : String
  region : String
  observation : String
  deriving DecidableEq, Repr

/-- The six payload fields of `proof-frame-index-plan-v1`. -/
structure GeneratedFrameIndexPlan where
  operation : String
  actionIndex : Nat
  machine : String
  carrier : String
  validation : String
  region : String
  deriving DecidableEq, Repr

/-- Generic logical sequences owned by the admitted workspace machines. -/
inductive WorkspaceSequenceRole where
  | evaluationStack
  | actualArguments
  | requiredBinderIdentifiers
  | orderedPremiseRows
  | binderOccurrenceCounts
  | requiredBinderIndex
  | premiseLabelIndex
  | bindingSchemas
  | premiseSchemas
  | apartnessPairs
  | orderedPremises
  | preparedBindings
  | preparedPremises
  | preparedActionCases
  | declarationSeenIndex
  | declarationPromotedIndex
  | promotedDeclarations
  | declarationControl
  | preparedControl
  | evidenceArena
  | evidenceNodes
  | canonicalConstructionCache
  | preparedValues
  | savedValues
  | actionRegisters
  deriving DecidableEq, Repr

/-- The generated carrier code selects a closed, vocabulary-neutral inventory.
Adding a new physical workspace class therefore requires an explicit semantic
case rather than being accepted as an arbitrary string. -/
def workspaceCarrierRoles : String → Option (List WorkspaceSequenceRole)
  | "stack-proof-call-workspace-v1" =>
      some [.evaluationStack, .actualArguments, .requiredBinderIdentifiers,
        .orderedPremiseRows, .bindingSchemas, .premiseSchemas,
        .apartnessPairs, .orderedPremises, .preparedBindings,
        .preparedPremises, .preparedActionCases,
        .declarationSeenIndex, .declarationPromotedIndex,
        .promotedDeclarations,
        .declarationControl, .preparedControl,
        .evidenceArena, .evidenceNodes, .canonicalConstructionCache]
  | "indexed-stack-proof-call-workspace-v1" =>
      some [.evaluationStack, .actualArguments, .requiredBinderIdentifiers,
        .orderedPremiseRows, .binderOccurrenceCounts, .preparedValues,
        .savedValues, .requiredBinderIndex, .premiseLabelIndex,
        .bindingSchemas, .premiseSchemas, .apartnessPairs,
        .orderedPremises, .preparedBindings, .preparedPremises,
        .preparedActionCases, .declarationControl, .preparedControl,
        .declarationSeenIndex, .declarationPromotedIndex,
        .promotedDeclarations,
        .evidenceArena,
        .evidenceNodes, .canonicalConstructionCache]
  | "action-call-workspace-v1" => some [.actionRegisters]
  | _ => none

/-- Decode exactly one generated workspace-plan payload. -/
def decodeGeneratedWorkspacePlan :
    List CallPlanField → Option GeneratedWorkspacePlan
  | [.symbol operation, .natural actionIndex, .symbol machine,
      .symbol carrier, .symbol region, .symbol observation] =>
      some {
        operation := operation
        actionIndex := actionIndex
        machine := machine
        carrier := carrier
        region := region
        observation := observation }
  | _ => none

def decodeGeneratedFrameIndexPlan :
    List CallPlanField → Option GeneratedFrameIndexPlan
  | [.symbol operation, .natural actionIndex, .symbol machine,
      .symbol carrier, .symbol validation, .symbol region] =>
      some {
        operation := operation
        actionIndex := actionIndex
        machine := machine
        carrier := carrier
        validation := validation
        region := region }
  | _ => none

/-- The source-call record establishes identity, call lifetime, and the value
observation boundary.  Its proof-sequence layout is intentionally not treated
as the layout of internal scratch values. -/
def GeneratedCallPlan.admitsReusableCall
    (plan : GeneratedCallPlan) (operation : String) (actionIndex : Nat)
    (machine region : String) : Bool :=
  plan.operation == operation &&
    plan.actionIndex == actionIndex &&
    plan.machine == machine &&
    plan.region == region &&
    region == "proof-call-region-v1" &&
    plan.observation == "proof-verdict-only-v1"

/-- The independently generated workspace record selects the closed generic
machine realization that owns and resets its physical carriers. -/
def GeneratedWorkspacePlan.admitsReusableWorkspace
    (plan : GeneratedWorkspacePlan) (operation : String)
    (actionIndex : Nat) (machine carrier region : String) : Bool :=
  plan.operation == operation &&
    plan.actionIndex == actionIndex &&
    plan.machine == machine &&
    plan.carrier == carrier &&
    (workspaceCarrierRoles plan.carrier).isSome &&
    plan.region == region &&
    region == "proof-call-region-v1" &&
    plan.observation == "proof-verdict-only-v1"

/-- The generated record selects the concrete realization of the independently
proved monotone unique-index optimization. -/
def GeneratedFrameIndexPlan.admitsMonotoneUniqueIndex
    (plan : GeneratedFrameIndexPlan) (operation : String)
    (actionIndex : Nat) (machine region : String) : Bool :=
  plan.operation == operation &&
    plan.actionIndex == actionIndex &&
    plan.machine == machine &&
    plan.carrier == "u32-open-addressed-index-v1" &&
    plan.validation == "duplicate-reject-v1" &&
    plan.region == region &&
    region == "proof-call-region-v1"

/-- Decode both generated records and classify them as the abstract
lifetime/effect certificate used by `compileObservable?`.  Agreement between
the records is checked explicitly. -/
def admitGeneratedCallPlan?
    (callFields workspaceFields : List CallPlanField)
    (operation : String) (actionIndex : Nat)
    (machine carrier region : String) : Option ReusePlan := do
  let call ← decodeGeneratedCallPlan callFields
  let workspace ← decodeGeneratedWorkspacePlan workspaceFields
  if call.admitsReusableCall operation actionIndex machine region &&
      workspace.admitsReusableWorkspace operation actionIndex machine
        carrier region &&
      call.operation == workspace.operation &&
      call.actionIndex == workspace.actionIndex &&
      call.machine == workspace.machine &&
      call.region == workspace.region &&
      call.observation == workspace.observation then
    some reusableCallPlan
  else none

/-- An indexed workspace may use its resettable finite maps only when the
independently generated frame-index record agrees with the call and workspace
records. -/
def admitGeneratedIndexedCallPlan?
    (callFields workspaceFields frameIndexFields : List CallPlanField)
    (operation : String) (actionIndex : Nat)
    (machine carrier region : String) : Option ReusePlan := do
  let reuse ← admitGeneratedCallPlan? callFields workspaceFields operation
    actionIndex machine carrier region
  let workspace ← decodeGeneratedWorkspacePlan workspaceFields
  let index ← decodeGeneratedFrameIndexPlan frameIndexFields
  if index.admitsMonotoneUniqueIndex operation actionIndex machine region &&
      workspace.operation == index.operation &&
      workspace.actionIndex == index.actionIndex &&
      workspace.machine == index.machine &&
      workspace.region == index.region then
    some reuse
  else none

theorem admitGeneratedCallPlan?_supportsReuse
    (callFields workspaceFields : List CallPlanField)
    (operation : String) (actionIndex : Nat)
    (machine carrier region : String) (plan : ReusePlan)
    (accepted : admitGeneratedCallPlan? callFields workspaceFields operation
      actionIndex machine carrier region = some plan) :
    plan.supportsReuse = true := by
  rw [admitGeneratedCallPlan?] at accepted
  obtain ⟨call, _callDecoded, accepted⟩ :=
    Option.bind_eq_some_iff.mp accepted
  obtain ⟨workspace, _workspaceDecoded, accepted⟩ :=
    Option.bind_eq_some_iff.mp accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst plan
    rfl
  · contradiction

theorem admitGeneratedIndexedCallPlan?_supportsReuse
    (callFields workspaceFields frameIndexFields : List CallPlanField)
    (operation : String) (actionIndex : Nat)
    (machine carrier region : String) (plan : ReusePlan)
    (accepted : admitGeneratedIndexedCallPlan? callFields workspaceFields
      frameIndexFields operation actionIndex machine carrier region =
      some plan) :
    plan.supportsReuse = true := by
  rw [admitGeneratedIndexedCallPlan?] at accepted
  obtain ⟨reuse, reuseAccepted, accepted⟩ :=
    Option.bind_eq_some_iff.mp accepted
  obtain ⟨_workspace, _workspaceDecoded, accepted⟩ :=
    Option.bind_eq_some_iff.mp accepted
  obtain ⟨_index, _indexDecoded, accepted⟩ :=
    Option.bind_eq_some_iff.mp accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst plan
    exact admitGeneratedCallPlan?_supportsReuse
      callFields workspaceFields operation actionIndex machine carrier region
      reuse reuseAccepted
  · contradiction

/-- The wire-level certificate selects the already-proved reusable-buffer
realization; it cannot create a second, unproved optimization path. -/
def compileGeneratedCall?
    (callFields workspaceFields : List CallPlanField)
    (operation : String) (actionIndex : Nat)
    (machine carrier region : String)
    (source : SequenceObservableProgram Value Observation) :
    Option (ReusableSequenceObservableProgram Value Observation) := do
  let plan ← admitGeneratedCallPlan? callFields workspaceFields operation
    actionIndex machine carrier region
  compileSequenceObservable? plan source

theorem compileGeneratedCall?_exact
    (callFields workspaceFields : List CallPlanField)
    (operation : String) (actionIndex : Nat)
    (machine carrier region : String)
    (source : SequenceObservableProgram Value Observation)
    (artifact : ReusableSequenceObservableProgram Value Observation)
    (accepted : compileGeneratedCall? callFields workspaceFields operation
      actionIndex machine carrier region source = some artifact) :
    observeReusableSequences artifact = observeFreshSequences source := by
  cases admitted : admitGeneratedCallPlan? callFields workspaceFields
      operation actionIndex machine carrier region with
  | none => simp [compileGeneratedCall?, admitted] at accepted
  | some plan =>
      have lowered : compileSequenceObservable? plan source = some artifact := by
        simpa [compileGeneratedCall?, admitted] using accepted
      exact compileSequenceObservable?_exact plan source artifact lowered

theorem compileGeneratedCall?_allocationCount_le
    (callFields workspaceFields : List CallPlanField)
    (operation : String) (actionIndex : Nat)
    (machine carrier region : String)
    (source : SequenceObservableProgram Value Observation)
    (artifact : ReusableSequenceObservableProgram Value Observation)
    (accepted : compileGeneratedCall? callFields workspaceFields operation
      actionIndex machine carrier region source = some artifact) :
    reusableSequenceAllocationCount artifact.calls ≤
      freshSequenceAllocationCount source.calls := by
  cases admitted : admitGeneratedCallPlan? callFields workspaceFields
      operation actionIndex machine carrier region with
  | none => simp [compileGeneratedCall?, admitted] at accepted
  | some plan =>
      have lowered : compileSequenceObservable? plan source = some artifact := by
        simpa [compileGeneratedCall?, admitted] using accepted
      exact compileSequenceObservable?_allocationCount_le
        plan source artifact lowered

/-! ## Independent positive and negative canaries -/

private def slot3 (value : Nat) (bound : value < 3) : Fin 3 :=
  ⟨value, bound⟩

private def binderTransactions : List (Transaction 3 String) :=
  [[(slot3 0 (by omega), "x"), (slot3 2 (by omega), "z")],
   [(slot3 1 (by omega), "y")]]

/-- A binder environment does not leak an earlier binder through reuse. -/
example : executeReusable binderTransactions =
    [[some "x", none, some "z"], [none, some "y", none]] := by
  decide

private def actionTransactions : List (Transaction 2 Nat) :=
  [[(⟨1, by omega⟩, 7)], [(⟨0, by omega⟩, 9)]]

/-- Parser/action registers independently exercise the same reset law. -/
example : executeReusable actionTransactions =
    [[none, some 7], [some 9, none]] := by
  decide

private def verdictProgram : ObservableProgram 2 Nat Bool :=
  { transactions := actionTransactions
    observe := fun slots => slots.any (· == some 9) }

private def sequenceVerdictProgram : SequenceObservableProgram Nat Bool :=
  { calls := [[7, 4], [], [9]]
    observe := fun values => values.contains 9 }

private def regionAttempts : List (RegionAttempt Nat Nat) :=
  [.success [1, 2] (fun values => values.sum),
   .failure [99, 100],
   .success [7] (fun values => values.sum)]

/-- Partial allocations from a failed call are not published and cannot
affect the next successful observation. -/
example :
    (executeReusableRegionAttemptsFrom regionAttempts
      (emptySequenceBuffer : SequenceBuffer Nat)).1 =
      [some 3, none, some 7] := by
  decide

private def proofCallFields : List CallPlanField :=
  [.symbol "check-article-v7", .natural 14,
   .symbol "stack-machine-alpha", .symbol "ProofCarrier",
   .symbol "ProvableCarrier", .symbol "proof-call-region-v1",
   .symbol "flat-symbol-id-vector-v1",
   .symbol "proof-verdict-only-v1"]

private def proofWorkspaceFields : List CallPlanField :=
  [.symbol "check-article-v7", .natural 14,
   .symbol "stack-machine-alpha",
   .symbol "stack-proof-call-workspace-v1",
   .symbol "proof-call-region-v1",
   .symbol "proof-verdict-only-v1"]

private def indexedProofWorkspaceFields : List CallPlanField :=
  [.symbol "check-article-v7", .natural 14,
   .symbol "stack-machine-alpha",
   .symbol "indexed-stack-proof-call-workspace-v1",
   .symbol "proof-call-region-v1",
   .symbol "proof-verdict-only-v1"]

private def proofFrameIndexFields : List CallPlanField :=
  [.symbol "check-article-v7", .natural 14,
   .symbol "stack-machine-alpha",
   .symbol "u32-open-addressed-index-v1",
   .symbol "duplicate-reject-v1",
   .symbol "proof-call-region-v1"]

example : workspaceCarrierRoles "stack-proof-call-workspace-v1" =
    some [.evaluationStack, .actualArguments, .requiredBinderIdentifiers,
      .orderedPremiseRows, .bindingSchemas, .premiseSchemas,
      .apartnessPairs, .orderedPremises, .preparedBindings,
      .preparedPremises, .preparedActionCases,
      .declarationSeenIndex, .declarationPromotedIndex,
      .promotedDeclarations,
      .declarationControl, .preparedControl,
      .evidenceArena, .evidenceNodes, .canonicalConstructionCache] := by
  rfl

example : workspaceCarrierRoles "indexed-stack-proof-call-workspace-v1" =
    some [.evaluationStack, .actualArguments, .requiredBinderIdentifiers,
      .orderedPremiseRows, .binderOccurrenceCounts, .preparedValues,
      .savedValues, .requiredBinderIndex, .premiseLabelIndex,
      .bindingSchemas, .premiseSchemas, .apartnessPairs,
      .orderedPremises, .preparedBindings, .preparedPremises,
      .preparedActionCases, .declarationControl, .preparedControl,
      .declarationSeenIndex, .declarationPromotedIndex,
      .promotedDeclarations,
      .evidenceArena,
      .evidenceNodes, .canonicalConstructionCache] := by
  rfl

/-- The indexed workspace and finite-map realization require agreeing,
independently generated records. -/
example :
    (admitGeneratedIndexedCallPlan? proofCallFields
      indexedProofWorkspaceFields proofFrameIndexFields
      "check-article-v7" 14 "stack-machine-alpha"
      "indexed-stack-proof-call-workspace-v1" "proof-call-region-v1").isSome =
      true := by
  decide

/-- An overwrite policy cannot select the duplicate-rejecting realization. -/
example :
    (admitGeneratedIndexedCallPlan? proofCallFields
      indexedProofWorkspaceFields
      (proofFrameIndexFields.take 4 ++
        [.symbol "overwrite-v1", .symbol "proof-call-region-v1"])
      "check-article-v7" 14 "stack-machine-alpha"
      "indexed-stack-proof-call-workspace-v1" "proof-call-region-v1").isSome =
      false := by
  decide

/-- A generated proof-style call record selects the certified lowering. -/
example :
    (compileGeneratedCall? proofCallFields proofWorkspaceFields
      "check-article-v7" 14 "stack-machine-alpha"
      "stack-proof-call-workspace-v1" "proof-call-region-v1"
      sequenceVerdictProgram).isSome = true := by
  decide

/-- The same machinery is independent of guest operation and machine names. -/
example :
    (admitGeneratedCallPlan?
      [.symbol "parse-actions", .natural 3, .symbol "cursor-machine",
       .symbol "ActionCarrier", .symbol "AcceptedAction",
       .symbol "proof-call-region-v1",
       .symbol "flat-symbol-id-vector-v1",
       .symbol "proof-verdict-only-v1"]
      [.symbol "parse-actions", .natural 3, .symbol "cursor-machine",
       .symbol "action-call-workspace-v1",
       .symbol "proof-call-region-v1",
       .symbol "proof-verdict-only-v1"]
      "parse-actions" 3 "cursor-machine" "action-call-workspace-v1"
      "proof-call-region-v1").isSome =
      true := by
  decide

/-- A reference-valued observation cannot license reset-and-reuse. -/
example :
    (admitGeneratedCallPlan?
      (proofCallFields.dropLast ++ [.symbol "returns-buffer-reference-v1"])
      proofWorkspaceFields "check-article-v7" 14 "stack-machine-alpha"
      "stack-proof-call-workspace-v1"
      "proof-call-region-v1").isSome = false := by
  decide

/-- A malformed field kind fails before lifetime classification. -/
example :
    (admitGeneratedCallPlan?
      [.symbol "check-article-v7", .symbol "fourteen"]
      proofWorkspaceFields "check-article-v7" 14 "stack-machine-alpha"
      "stack-proof-call-workspace-v1"
      "proof-call-region-v1").isSome = false := by
  decide

/-- A different generated workspace class cannot silently select this
physical realization. -/
example :
    (admitGeneratedCallPlan? proofCallFields proofWorkspaceFields
      "check-article-v7" 14 "stack-machine-alpha"
      "indexed-stack-proof-call-workspace-v1"
      "proof-call-region-v1").isSome = false := by
  decide

/-- A call-local, value-returning proof-style verdict is admitted. -/
example :
    (compileObservable?
      { lifetime := .callLocal, boundary := .value }
      verdictProgram).isSome = true := by
  decide

/-- A parser-style retained reference is not silently admitted for reuse. -/
example :
    (compileObservable?
      { lifetime := .callLocal, boundary := .reference }
      verdictProgram).isSome = false := by
  decide

/-- A persistent buffer lies outside the call-local optimization fragment. -/
example :
    (compileObservable?
      { lifetime := .retained, boundary := .value }
      verdictProgram).isSome = false := by
  decide

/-- Deliberately omitting reset exposes the stale-slot failure mode. -/
def executeWithoutResetFrom [DecidableEq (Fin width)] :
    List (Transaction width Value) -> Buffer width Value ->
      List (List (Option Value))
  | [], _ => []
  | transaction :: transactions, buffer =>
      let completed := runFrom buffer transaction
      snapshot completed :: executeWithoutResetFrom transactions completed

example :
    executeWithoutResetFrom binderTransactions (emptyBuffer : Buffer 3 String) !=
      executeFresh binderTransactions := by
  decide

end Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation
