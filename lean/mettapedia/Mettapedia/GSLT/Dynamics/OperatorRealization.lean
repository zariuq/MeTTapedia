import Mettapedia.Machines.RevisionedOccurrenceStore

/-!
# Open principles for executable operator realizations

This module gives a small semantic waist for executing an operator against a
revision-scoped snapshot:

```text
Snapshot × OperatorPlan → Delta × Receipt
```

The definitions are deliberately *not* a final ABI, an initial object, or a
claim that these laws completely characterize a realization.  They record four
principles that current native and persistent-store realizations need to share:

* authored occurrence order and multiplicity remain explicit;
* stale plans and receipts are rejected;
* declining parallel execution selects a serialized realization rather than
  changing the language meaning;
* heterogeneous transfers compose only at matching backend/revision
  boundaries, while retaining every intermediate delta and receipt.

Physical snapshots, operator encodings, hashes, scheduling policies, costs,
and richer evidence may extend these records.  `AcceptanceRefinement` states
the obligation for such an extension: accepted rich evidence must erase to
accepted core evidence.  Thus the module guides implementations without
closing the design space around its present vocabulary.
-/

namespace Mettapedia.GSLT.Dynamics.OperatorRealization

open Mettapedia.Machines

set_option autoImplicit false

/-- A semantic snapshot is a revision-scoped occurrence store.  Here
`Backend` denotes a unique backend/store endpoint, not merely an implementation
family.  A system with several spaces on one engine can instantiate it with a
pair such as `(BackendKind × StoreId)`.  A physical backend may carry indexes,
roots, generations, or reclamation state in a richer type and erase to this
view. -/
abbrev Snapshot (Backend Revision Payload : Type) :=
  RevisionedStoreView Backend Revision Payload

/-- Occurrence identity is tied to both a backend/store and a revision. -/
abbrev OccurrenceId (Backend Revision : Type) :=
  StoreOccurrenceId Backend Revision

/-- Whether an accepted execution used a parallel plan or the required
serialized fallback. -/
inductive ExecutionMode where
  | parallel
  | serialized
deriving DecidableEq, Repr

/-- The backend-neutral information that must survive operator compilation.
The occurrence list is ordered and may contain repetitions. -/
structure OperatorPlan (Backend Revision Observer PlanId : Type) where
  id : PlanId
  observer : Observer
  sourceBackend : Backend
  targetBackend : Backend
  sourceRevision : Revision
  authoredOccurrences : List (OccurrenceId Backend Revision)

/-- A semantic delta names its source and target boundary and retains emitted
occurrences in order.  `id` may be realized by a structural identifier or a
digest, but the core does not prescribe either. -/
structure Delta (Backend Revision Payload DeltaId : Type) where
  id : DeltaId
  sourceBackend : Backend
  targetBackend : Backend
  sourceRevision : Revision
  targetRevision : Revision
  entries : List (OccurrenceId Backend Revision × Payload)

/-- Evidence returned by one realization step.  The receipt binds the plan,
named observer, exact boundary, exact delta identity, authored occurrence
sequence, and emitted occurrence sequence. -/
structure Receipt (Backend Revision Observer PlanId DeltaId : Type) where
  planId : PlanId
  observer : Observer
  sourceBackend : Backend
  targetBackend : Backend
  sourceRevision : Revision
  targetRevision : Revision
  deltaId : DeltaId
  mode : ExecutionMode
  authoredOccurrences : List (OccurrenceId Backend Revision)
  emittedOccurrences : List (OccurrenceId Backend Revision)

namespace Snapshot

variable {Backend Revision Payload : Type}

/-- A plan is scoped to a snapshot exactly when its source boundary agrees and
every referenced occurrence resolves in that snapshot. -/
def wellScoped [DecidableEq Backend] [DecidableEq Revision]
    (snapshot : Snapshot Backend Revision Payload)
    {Observer PlanId : Type}
    (plan : OperatorPlan Backend Revision Observer PlanId) : Bool :=
  decide (snapshot.storeId = plan.sourceBackend) &&
    decide (snapshot.revision = plan.sourceRevision) &&
    plan.authoredOccurrences.all fun occurrence =>
      (snapshot.resolve occurrence).isSome

@[simp] theorem wellScoped_wrong_revision [DecidableEq Backend]
    [DecidableEq Revision]
    (snapshot : Snapshot Backend Revision Payload)
    {Observer PlanId : Type}
    (plan : OperatorPlan Backend Revision Observer PlanId)
    (stale : snapshot.revision ≠ plan.sourceRevision) :
    snapshot.wellScoped plan = false := by
  simp [wellScoped, stale]

@[simp] theorem wellScoped_wrong_backend [DecidableEq Backend]
    [DecidableEq Revision]
    (snapshot : Snapshot Backend Revision Payload)
    {Observer PlanId : Type}
    (plan : OperatorPlan Backend Revision Observer PlanId)
    (wrong : snapshot.storeId ≠ plan.sourceBackend) :
    snapshot.wellScoped plan = false := by
  simp [wellScoped, wrong]

end Snapshot

namespace Delta

variable {Backend Revision Payload DeltaId : Type}

/-- Every emitted occurrence must be scoped to the delta's target boundary. -/
def wellScoped [DecidableEq Backend] [DecidableEq Revision]
    (delta : Delta Backend Revision Payload DeltaId) : Bool :=
  delta.entries.all fun entry =>
    decide (entry.1.read.storeId = delta.targetBackend) &&
      decide (entry.1.read.revision = delta.targetRevision)

end Delta

/-- Receipt identities agree with the plan and delta. -/
def identityAligned
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    (plan : OperatorPlan Backend Revision Observer PlanId)
    (delta : Delta Backend Revision Payload DeltaId)
    (receipt : Receipt Backend Revision Observer PlanId DeltaId) : Bool :=
  decide (
    delta.sourceBackend = plan.sourceBackend ∧
    delta.targetBackend = plan.targetBackend ∧
    receipt.planId = plan.id ∧
    receipt.observer = plan.observer ∧
    receipt.sourceBackend = delta.sourceBackend ∧
    receipt.targetBackend = delta.targetBackend ∧
    receipt.sourceRevision = delta.sourceRevision ∧
    receipt.targetRevision = delta.targetRevision ∧
    receipt.deltaId = delta.id)

/-- Ordered occurrence sequences in the receipt agree exactly with the plan
and delta.  Exact list equality preserves both order and multiplicity. -/
def occurrenceEvidenceAligned
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    (plan : OperatorPlan Backend Revision Observer PlanId)
    (delta : Delta Backend Revision Payload DeltaId)
    (receipt : Receipt Backend Revision Observer PlanId DeltaId) : Bool :=
  decide (
    receipt.authoredOccurrences = plan.authoredOccurrences ∧
    receipt.emittedOccurrences = delta.entries.map Prod.fst)

/-- A parallel receipt is allowed only when parallel admission succeeded.  A
serialized receipt is allowed in either case, so a backend may conservatively
serialize an otherwise parallelizable operator. -/
def modeAllowed (parallelAdmitted : Bool) (mode : ExecutionMode) : Bool :=
  parallelAdmitted || decide (mode = .serialized)

/-- Executable acceptance checker for the open realization principles. -/
def accepts
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    (parallelAdmitted : Bool)
    (snapshot : Snapshot Backend Revision Payload)
    (plan : OperatorPlan Backend Revision Observer PlanId)
    (delta : Delta Backend Revision Payload DeltaId)
    (receipt : Receipt Backend Revision Observer PlanId DeltaId) : Bool :=
  snapshot.wellScoped plan &&
    delta.wellScoped &&
    decide (delta.sourceRevision = snapshot.revision) &&
    identityAligned plan delta receipt &&
    occurrenceEvidenceAligned plan delta receipt &&
    modeAllowed parallelAdmitted receipt.mode

theorem accepts_eq_true_iff
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    {parallelAdmitted : Bool}
    {snapshot : Snapshot Backend Revision Payload}
    {plan : OperatorPlan Backend Revision Observer PlanId}
    {delta : Delta Backend Revision Payload DeltaId}
    {receipt : Receipt Backend Revision Observer PlanId DeltaId} :
    accepts parallelAdmitted snapshot plan delta receipt = true ↔
      snapshot.wellScoped plan = true ∧
      delta.wellScoped = true ∧
      delta.sourceRevision = snapshot.revision ∧
      identityAligned plan delta receipt = true ∧
      occurrenceEvidenceAligned plan delta receipt = true ∧
      modeAllowed parallelAdmitted receipt.mode = true := by
  simp [accepts, and_assoc]

/-! ## Consequences of accepted evidence -/

theorem accepted_authored_order
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    {parallelAdmitted : Bool}
    {snapshot : Snapshot Backend Revision Payload}
    {plan : OperatorPlan Backend Revision Observer PlanId}
    {delta : Delta Backend Revision Payload DeltaId}
    {receipt : Receipt Backend Revision Observer PlanId DeltaId}
    (accepted : accepts parallelAdmitted snapshot plan delta receipt = true) :
    receipt.authoredOccurrences = plan.authoredOccurrences := by
  have aligned := (accepts_eq_true_iff.mp accepted).2.2.2.2.1
  have conjunction :
      receipt.authoredOccurrences = plan.authoredOccurrences ∧
      receipt.emittedOccurrences = delta.entries.map Prod.fst := by
    simpa [occurrenceEvidenceAligned] using aligned
  exact conjunction.1

theorem accepted_emitted_order
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    {parallelAdmitted : Bool}
    {snapshot : Snapshot Backend Revision Payload}
    {plan : OperatorPlan Backend Revision Observer PlanId}
    {delta : Delta Backend Revision Payload DeltaId}
    {receipt : Receipt Backend Revision Observer PlanId DeltaId}
    (accepted : accepts parallelAdmitted snapshot plan delta receipt = true) :
    receipt.emittedOccurrences = delta.entries.map Prod.fst := by
  have aligned := (accepts_eq_true_iff.mp accepted).2.2.2.2.1
  have conjunction :
      receipt.authoredOccurrences = plan.authoredOccurrences ∧
      receipt.emittedOccurrences = delta.entries.map Prod.fst := by
    simpa [occurrenceEvidenceAligned] using aligned
  exact conjunction.2

/-- Accepted evidence carries the identifier of the compiled operator plan. -/
theorem accepted_planId
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    {parallelAdmitted : Bool}
    {snapshot : Snapshot Backend Revision Payload}
    {plan : OperatorPlan Backend Revision Observer PlanId}
    {delta : Delta Backend Revision Payload DeltaId}
    {receipt : Receipt Backend Revision Observer PlanId DeltaId}
    (accepted : accepts parallelAdmitted snapshot plan delta receipt = true) :
    receipt.planId = plan.id := by
  have identities := (accepts_eq_true_iff.mp accepted).2.2.2.1
  have conjunction :
      delta.sourceBackend = plan.sourceBackend ∧
      delta.targetBackend = plan.targetBackend ∧
      receipt.planId = plan.id ∧
      receipt.observer = plan.observer ∧
      receipt.sourceBackend = delta.sourceBackend ∧
      receipt.targetBackend = delta.targetBackend ∧
      receipt.sourceRevision = delta.sourceRevision ∧
      receipt.targetRevision = delta.targetRevision ∧
      receipt.deltaId = delta.id := by
    simpa [identityAligned] using identities
  exact conjunction.2.2.1

/-- Accepted evidence names exactly the observer attached to the compiled
operator plan. -/
theorem accepted_observer
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    {parallelAdmitted : Bool}
    {snapshot : Snapshot Backend Revision Payload}
    {plan : OperatorPlan Backend Revision Observer PlanId}
    {delta : Delta Backend Revision Payload DeltaId}
    {receipt : Receipt Backend Revision Observer PlanId DeltaId}
    (accepted : accepts parallelAdmitted snapshot plan delta receipt = true) :
    receipt.observer = plan.observer := by
  have identities := (accepts_eq_true_iff.mp accepted).2.2.2.1
  have conjunction :
      delta.sourceBackend = plan.sourceBackend ∧
      delta.targetBackend = plan.targetBackend ∧
      receipt.planId = plan.id ∧
      receipt.observer = plan.observer ∧
      receipt.sourceBackend = delta.sourceBackend ∧
      receipt.targetBackend = delta.targetBackend ∧
      receipt.sourceRevision = delta.sourceRevision ∧
      receipt.targetRevision = delta.targetRevision ∧
      receipt.deltaId = delta.id := by
    simpa [identityAligned] using identities
  exact conjunction.2.2.2.1

/-- Accepted evidence binds the exact semantic delta identity. -/
theorem accepted_deltaId
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    {parallelAdmitted : Bool}
    {snapshot : Snapshot Backend Revision Payload}
    {plan : OperatorPlan Backend Revision Observer PlanId}
    {delta : Delta Backend Revision Payload DeltaId}
    {receipt : Receipt Backend Revision Observer PlanId DeltaId}
    (accepted : accepts parallelAdmitted snapshot plan delta receipt = true) :
    receipt.deltaId = delta.id := by
  have identities := (accepts_eq_true_iff.mp accepted).2.2.2.1
  have conjunction :
      delta.sourceBackend = plan.sourceBackend ∧
      delta.targetBackend = plan.targetBackend ∧
      receipt.planId = plan.id ∧
      receipt.observer = plan.observer ∧
      receipt.sourceBackend = delta.sourceBackend ∧
      receipt.targetBackend = delta.targetBackend ∧
      receipt.sourceRevision = delta.sourceRevision ∧
      receipt.targetRevision = delta.targetRevision ∧
      receipt.deltaId = delta.id := by
    simpa [identityAligned] using identities
  exact conjunction.2.2.2.2.2.2.2.2

theorem accepted_authored_multiplicity
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    {parallelAdmitted : Bool}
    {snapshot : Snapshot Backend Revision Payload}
    {plan : OperatorPlan Backend Revision Observer PlanId}
    {delta : Delta Backend Revision Payload DeltaId}
    {receipt : Receipt Backend Revision Observer PlanId DeltaId}
    (accepted : accepts parallelAdmitted snapshot plan delta receipt = true)
    (occurrence : OccurrenceId Backend Revision) :
    receipt.authoredOccurrences.count occurrence =
      plan.authoredOccurrences.count occurrence := by
  rw [accepted_authored_order accepted]

theorem rejects_stale_plan
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    (parallelAdmitted : Bool)
    (snapshot : Snapshot Backend Revision Payload)
    (plan : OperatorPlan Backend Revision Observer PlanId)
    (delta : Delta Backend Revision Payload DeltaId)
    (receipt : Receipt Backend Revision Observer PlanId DeltaId)
    (stale : snapshot.revision ≠ plan.sourceRevision) :
    accepts parallelAdmitted snapshot plan delta receipt = false := by
  simp [accepts, Snapshot.wellScoped, stale]

theorem rejects_stale_receipt
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    (parallelAdmitted : Bool)
    (snapshot : Snapshot Backend Revision Payload)
    (plan : OperatorPlan Backend Revision Observer PlanId)
    (delta : Delta Backend Revision Payload DeltaId)
    (receipt : Receipt Backend Revision Observer PlanId DeltaId)
    (stale : receipt.sourceRevision ≠ snapshot.revision) :
    accepts parallelAdmitted snapshot plan delta receipt = false := by
  by_contra accepted
  have acceptedTrue :
      accepts parallelAdmitted snapshot plan delta receipt = true :=
    Bool.eq_true_of_not_eq_false accepted
  have components := accepts_eq_true_iff.mp acceptedTrue
  have identities : identityAligned plan delta receipt = true :=
    components.2.2.2.1
  have sourceDelta : delta.sourceRevision = snapshot.revision :=
    components.2.2.1
  have receiptDelta : receipt.sourceRevision = delta.sourceRevision := by
    have conjunction :
        delta.sourceBackend = plan.sourceBackend ∧
        delta.targetBackend = plan.targetBackend ∧
        receipt.planId = plan.id ∧
        receipt.observer = plan.observer ∧
        receipt.sourceBackend = delta.sourceBackend ∧
        receipt.targetBackend = delta.targetBackend ∧
        receipt.sourceRevision = delta.sourceRevision ∧
        receipt.targetRevision = delta.targetRevision ∧
        receipt.deltaId = delta.id := by
      simpa [identityAligned] using identities
    exact conjunction.2.2.2.2.2.2.1
  exact stale (receiptDelta.trans sourceDelta)

theorem rejects_unadmitted_parallel
    {Backend Revision Payload Observer PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    (snapshot : Snapshot Backend Revision Payload)
    (plan : OperatorPlan Backend Revision Observer PlanId)
    (delta : Delta Backend Revision Payload DeltaId)
    (receipt : Receipt Backend Revision Observer PlanId DeltaId)
    (parallel : receipt.mode = .parallel) :
    accepts false snapshot plan delta receipt = false := by
  simp [accepts, modeAllowed, parallel]

/-! ## Realizations and the serialization obligation -/

/-- An executable realization may choose its own parallel-safety proposition.
Parallel admission must imply that proposition.  Ill-scoped plans are rejected;
a well-scoped plan declined for parallel execution must still run through a
serialized path. -/
structure ExecutableRealization
    (Backend Revision Payload Observer PlanId DeltaId : Type)
    [DecidableEq Backend] [DecidableEq Revision] [DecidableEq Observer]
    [DecidableEq PlanId] [DecidableEq DeltaId]
    (ParallelSafe : Snapshot Backend Revision Payload →
      OperatorPlan Backend Revision Observer PlanId → Prop) where
  parallelAdmitted : Snapshot Backend Revision Payload →
    OperatorPlan Backend Revision Observer PlanId → Bool
  parallelSound : ∀ snapshot plan,
    parallelAdmitted snapshot plan = true → ParallelSafe snapshot plan
  run : Snapshot Backend Revision Payload →
    OperatorPlan Backend Revision Observer PlanId →
    Option (Delta Backend Revision Payload DeltaId ×
      Receipt Backend Revision Observer PlanId DeltaId)
  sound : ∀ snapshot plan delta receipt,
    run snapshot plan = some (delta, receipt) →
      accepts (parallelAdmitted snapshot plan) snapshot plan delta receipt = true
  rejectsIllScoped : ∀ snapshot plan,
    snapshot.wellScoped plan = false → run snapshot plan = none
  serializesDeclined : ∀ snapshot plan,
    snapshot.wellScoped plan = true →
    parallelAdmitted snapshot plan = false →
    ∃ delta receipt,
      run snapshot plan = some (delta, receipt) ∧
      receipt.mode = .serialized

namespace ExecutableRealization

variable {Backend Revision Payload Observer PlanId DeltaId : Type}
  [DecidableEq Backend] [DecidableEq Revision] [DecidableEq Observer]
  [DecidableEq PlanId] [DecidableEq DeltaId]
  {ParallelSafe : Snapshot Backend Revision Payload →
    OperatorPlan Backend Revision Observer PlanId → Prop}

/-- A realization cannot emit a parallel receipt without establishing its
declared parallel-safety proposition. -/
theorem parallelSafe_of_parallelReceipt
    (realization : ExecutableRealization Backend Revision Payload Observer
      PlanId DeltaId ParallelSafe)
    {snapshot : Snapshot Backend Revision Payload}
    {plan : OperatorPlan Backend Revision Observer PlanId}
    {delta : Delta Backend Revision Payload DeltaId}
    {receipt : Receipt Backend Revision Observer PlanId DeltaId}
    (ran : realization.run snapshot plan = some (delta, receipt))
    (parallel : receipt.mode = .parallel) :
    ParallelSafe snapshot plan := by
  have accepted := realization.sound snapshot plan delta receipt ran
  have allowed := (accepts_eq_true_iff.mp accepted).2.2.2.2.2
  have admitted : realization.parallelAdmitted snapshot plan = true := by
    simpa [modeAllowed, parallel] using allowed
  exact realization.parallelSound snapshot plan admitted

end ExecutableRealization

/-! ## Lossless heterogeneous transfer traces -/

/-- One transfer leg retains its delta and receipt rather than pretending that
arbitrary backend deltas have a universal merge algebra. -/
structure TransferLeg (Backend Revision Payload Observer PlanId DeltaId : Type) where
  delta : Delta Backend Revision Payload DeltaId
  receipt : Receipt Backend Revision Observer PlanId DeltaId

namespace TransferLeg

variable {Backend Revision Payload Observer PlanId DeltaId : Type}

/-- Turn an accepted execution output into one transfer leg.  The proof is
consumed at the semantic boundary; concrete certificate formats may retain it
or a checked encoding of it. -/
def ofAccepted [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    (parallelAdmitted : Bool)
    (snapshot : Snapshot Backend Revision Payload)
    (plan : OperatorPlan Backend Revision Observer PlanId)
    (delta : Delta Backend Revision Payload DeltaId)
    (receipt : Receipt Backend Revision Observer PlanId DeltaId)
    (_accepted : accepts parallelAdmitted snapshot plan delta receipt = true) :
    TransferLeg Backend Revision Payload Observer PlanId DeltaId :=
  ⟨delta, receipt⟩

/-- A raw leg is coherent when the receipt and delta name the same boundary and
delta identity. -/
def coherent [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq DeltaId]
    (leg : TransferLeg Backend Revision Payload Observer PlanId DeltaId) : Bool :=
  decide (
    leg.receipt.sourceBackend = leg.delta.sourceBackend ∧
    leg.receipt.targetBackend = leg.delta.targetBackend ∧
    leg.receipt.sourceRevision = leg.delta.sourceRevision ∧
    leg.receipt.targetRevision = leg.delta.targetRevision ∧
    leg.receipt.deltaId = leg.delta.id)

/-- Every leg constructed from accepted execution evidence is coherent. -/
theorem ofAccepted_coherent [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq Observer] [DecidableEq PlanId] [DecidableEq DeltaId]
    (parallelAdmitted : Bool)
    (snapshot : Snapshot Backend Revision Payload)
    (plan : OperatorPlan Backend Revision Observer PlanId)
    (delta : Delta Backend Revision Payload DeltaId)
    (receipt : Receipt Backend Revision Observer PlanId DeltaId)
    (accepted : accepts parallelAdmitted snapshot plan delta receipt = true) :
    (ofAccepted parallelAdmitted snapshot plan delta receipt accepted).coherent =
      true := by
  have identities := (accepts_eq_true_iff.mp accepted).2.2.2.1
  have conjunction :
      delta.sourceBackend = plan.sourceBackend ∧
      delta.targetBackend = plan.targetBackend ∧
      receipt.planId = plan.id ∧
      receipt.observer = plan.observer ∧
      receipt.sourceBackend = delta.sourceBackend ∧
      receipt.targetBackend = delta.targetBackend ∧
      receipt.sourceRevision = delta.sourceRevision ∧
      receipt.targetRevision = delta.targetRevision ∧
      receipt.deltaId = delta.id := by
    simpa [identityAligned] using identities
  simp [ofAccepted, coherent, conjunction.2.2.2.2.1,
    conjunction.2.2.2.2.2.1, conjunction.2.2.2.2.2.2.1,
    conjunction.2.2.2.2.2.2.2.1, conjunction.2.2.2.2.2.2.2.2]

end TransferLeg

/-- A nonempty, lossless chain of backend transfers. -/
structure TransferTrace (Backend Revision Payload Observer PlanId DeltaId : Type) where
  head : TransferLeg Backend Revision Payload Observer PlanId DeltaId
  tail : List (TransferLeg Backend Revision Payload Observer PlanId DeltaId)

namespace TransferTrace

variable {Backend Revision Payload Observer PlanId DeltaId : Type}

/-- All legs, in transfer order. -/
def legs (trace : TransferTrace Backend Revision Payload Observer PlanId DeltaId) :
    List (TransferLeg Backend Revision Payload Observer PlanId DeltaId) :=
  trace.head :: trace.tail

private def finalLeg
    (head : TransferLeg Backend Revision Payload Observer PlanId DeltaId) :
    List (TransferLeg Backend Revision Payload Observer PlanId DeltaId) →
    TransferLeg Backend Revision Payload Observer PlanId DeltaId
  | [] => head
  | next :: rest => finalLeg next rest

def sourceBackend
    (trace : TransferTrace Backend Revision Payload Observer PlanId DeltaId) :
    Backend :=
  trace.head.delta.sourceBackend

def sourceRevision
    (trace : TransferTrace Backend Revision Payload Observer PlanId DeltaId) :
    Revision :=
  trace.head.delta.sourceRevision

def targetBackend
    (trace : TransferTrace Backend Revision Payload Observer PlanId DeltaId) :
    Backend :=
  (finalLeg trace.head trace.tail).delta.targetBackend

def targetRevision
    (trace : TransferTrace Backend Revision Payload Observer PlanId DeltaId) :
    Revision :=
  (finalLeg trace.head trace.tail).delta.targetRevision

private def connectedFrom [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq DeltaId]
    (previous : TransferLeg Backend Revision Payload Observer PlanId DeltaId) :
    List (TransferLeg Backend Revision Payload Observer PlanId DeltaId) → Bool
  | [] => previous.coherent
  | next :: rest =>
      previous.coherent && next.coherent &&
        decide (previous.delta.targetBackend = next.delta.sourceBackend) &&
        decide (previous.delta.targetRevision = next.delta.sourceRevision) &&
        connectedFrom next rest

/-- Executable check that every leg is coherent and adjacent boundaries agree. -/
def wellFormed [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq DeltaId]
    (trace : TransferTrace Backend Revision Payload Observer PlanId DeltaId) : Bool :=
  connectedFrom trace.head trace.tail

/-- A singleton trace. -/
def singleton
    (leg : TransferLeg Backend Revision Payload Observer PlanId DeltaId) :
    TransferTrace Backend Revision Payload Observer PlanId DeltaId :=
  ⟨leg, []⟩

/-- Compose two lossless traces only when both are well formed and their middle
backend/revision boundaries agree.  The result retains every leg in order. -/
def compose? [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq DeltaId]
    (left right :
      TransferTrace Backend Revision Payload Observer PlanId DeltaId) :
    Option (TransferTrace Backend Revision Payload Observer PlanId DeltaId) :=
  let result : TransferTrace Backend Revision Payload Observer PlanId DeltaId :=
    ⟨left.head, left.tail ++ right.head :: right.tail⟩
  if left.wellFormed && right.wellFormed &&
      decide (left.targetBackend = right.sourceBackend) &&
      decide (left.targetRevision = right.sourceRevision) &&
      result.wellFormed then
    some result
  else
    none

theorem compose?_retains_legs [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq DeltaId]
    (left right result :
      TransferTrace Backend Revision Payload Observer PlanId DeltaId)
    (composed : compose? left right = some result) :
    result.legs = left.legs ++ right.legs := by
  simp only [compose?, legs] at composed ⊢
  split at composed
  · cases composed
    rfl
  · simp at composed

theorem compose?_wellFormed [DecidableEq Backend] [DecidableEq Revision]
    [DecidableEq DeltaId]
    (left right result :
      TransferTrace Backend Revision Payload Observer PlanId DeltaId)
    (composed : compose? left right = some result) :
    result.wellFormed = true := by
  simp only [compose?] at composed
  split at composed
  · rename_i condition
    simp only [Option.some.injEq] at composed
    cases composed
    simp_all
  · simp at composed

/-- Two independently accepted execution outputs compose whenever their
middle backend and revision agree.  This theorem is the semantic layer above
the raw executable trace checker. -/
theorem acceptedOutputs_compose
    [DecidableEq Backend] [DecidableEq Revision] [DecidableEq Observer]
    [DecidableEq PlanId] [DecidableEq DeltaId]
    {leftAdmitted rightAdmitted : Bool}
    (leftSnapshot rightSnapshot : Snapshot Backend Revision Payload)
    (leftPlan rightPlan : OperatorPlan Backend Revision Observer PlanId)
    (leftDelta rightDelta : Delta Backend Revision Payload DeltaId)
    (leftReceipt rightReceipt :
      Receipt Backend Revision Observer PlanId DeltaId)
    (leftAccepted : accepts leftAdmitted leftSnapshot leftPlan leftDelta
      leftReceipt = true)
    (rightAccepted : accepts rightAdmitted rightSnapshot rightPlan rightDelta
      rightReceipt = true)
    (backendMatches :
      leftDelta.targetBackend = rightDelta.sourceBackend)
    (revisionMatches :
      leftDelta.targetRevision = rightDelta.sourceRevision) :
    ∃ trace,
      compose?
        (singleton (TransferLeg.ofAccepted leftAdmitted leftSnapshot leftPlan
          leftDelta leftReceipt leftAccepted))
        (singleton (TransferLeg.ofAccepted rightAdmitted rightSnapshot rightPlan
          rightDelta rightReceipt rightAccepted)) = some trace := by
  let leftLeg := TransferLeg.ofAccepted leftAdmitted leftSnapshot leftPlan
    leftDelta leftReceipt leftAccepted
  let rightLeg := TransferLeg.ofAccepted rightAdmitted rightSnapshot rightPlan
    rightDelta rightReceipt rightAccepted
  refine ⟨⟨leftLeg, [rightLeg]⟩, ?_⟩
  have leftCoherent : leftLeg.coherent = true := by
    exact TransferLeg.ofAccepted_coherent leftAdmitted leftSnapshot leftPlan
      leftDelta leftReceipt leftAccepted
  have rightCoherent : rightLeg.coherent = true := by
    exact TransferLeg.ofAccepted_coherent rightAdmitted rightSnapshot rightPlan
      rightDelta rightReceipt rightAccepted
  have leftRawCoherent :
      (⟨leftDelta, leftReceipt⟩ :
        TransferLeg Backend Revision Payload Observer PlanId DeltaId).coherent =
        true := by
    simpa [leftLeg, TransferLeg.ofAccepted] using leftCoherent
  have rightRawCoherent :
      (⟨rightDelta, rightReceipt⟩ :
        TransferLeg Backend Revision Payload Observer PlanId DeltaId).coherent =
        true := by
    simpa [rightLeg, TransferLeg.ofAccepted] using rightCoherent
  simp [compose?, singleton, wellFormed, connectedFrom, leftLeg, rightLeg,
    TransferLeg.ofAccepted, leftRawCoherent, rightRawCoherent, backendMatches,
    revisionMatches,
    sourceBackend, sourceRevision, targetBackend, targetRevision, finalLeg]

end TransferTrace

/-! ## Open extension boundary -/

/-- Rich executable evidence refines the core when accepted rich artifacts
erase to accepted core artifacts.  This permits cost, provenance, capability,
backend-specific, and future observer fields without changing the core laws. -/
structure AcceptanceRefinement
    (Backend Revision Payload Observer PlanId DeltaId : Type)
    [DecidableEq Backend] [DecidableEq Revision] [DecidableEq Observer]
    [DecidableEq PlanId] [DecidableEq DeltaId]
    (RichSnapshot RichPlan RichDelta RichReceipt : Type)
    (richAccepts : Bool → RichSnapshot → RichPlan → RichDelta →
      RichReceipt → Bool) where
  eraseSnapshot : RichSnapshot → Snapshot Backend Revision Payload
  erasePlan : RichPlan → OperatorPlan Backend Revision Observer PlanId
  eraseDelta : RichDelta → Delta Backend Revision Payload DeltaId
  eraseReceipt : RichReceipt →
    Receipt Backend Revision Observer PlanId DeltaId
  preservesAcceptance : ∀ admitted snapshot plan delta receipt,
    richAccepts admitted snapshot plan delta receipt = true →
      accepts admitted (eraseSnapshot snapshot) (erasePlan plan)
        (eraseDelta delta) (eraseReceipt receipt) = true

/-! ## Executable positive and negative witnesses -/

namespace Example

inductive Backend where
  | native
  | pathMap
deriving DecidableEq, Repr

abbrev Revision := Nat
abbrev Payload := Unit
abbrev Observer := Bool
abbrev PlanId := Nat
abbrev DeltaId := Nat

def snapshot : Snapshot Backend Revision Payload :=
  ⟨.native, 7, [(), ()]⟩

def occurrence0 : OccurrenceId Backend Revision := snapshot.occurrenceId 0
def occurrence1 : OccurrenceId Backend Revision := snapshot.occurrenceId 1

def targetOccurrence (index : Nat) : OccurrenceId Backend Revision :=
  ⟨⟨.pathMap, 8⟩, index⟩

def plan : OperatorPlan Backend Revision Observer PlanId where
  id := 17
  observer := true
  sourceBackend := .native
  targetBackend := .pathMap
  sourceRevision := 7
  authoredOccurrences := [occurrence0, occurrence1]

def delta : Delta Backend Revision Payload DeltaId where
  id := 23
  sourceBackend := .native
  targetBackend := .pathMap
  sourceRevision := 7
  targetRevision := 8
  entries := [(targetOccurrence 0, ()), (targetOccurrence 1, ())]

def receipt : Receipt Backend Revision Observer PlanId DeltaId where
  planId := 17
  observer := true
  sourceBackend := .native
  targetBackend := .pathMap
  sourceRevision := 7
  targetRevision := 8
  deltaId := 23
  mode := .parallel
  authoredOccurrences := [occurrence0, occurrence1]
  emittedOccurrences := [targetOccurrence 0, targetOccurrence 1]

/-- Positive witness: two equal payloads remain two ordered occurrences. -/
theorem ordered_duplicates_accepted :
    accepts true snapshot plan delta receipt = true := by
  decide

/-- Negative order witness: swapping the receipt's occurrence order is
rejected even though the occurrence bag is unchanged. -/
theorem reordered_receipt_rejected :
    accepts true snapshot plan delta
      { receipt with authoredOccurrences := [occurrence1, occurrence0] } =
        false := by
  decide

/-- Negative multiplicity witness: dropping one equal-payload occurrence is
rejected. -/
theorem dropped_duplicate_rejected :
    accepts true snapshot plan delta
      { receipt with authoredOccurrences := [occurrence0] } = false := by
  decide

def stalePlan : OperatorPlan Backend Revision Observer PlanId :=
  { plan with sourceRevision := 6 }

/-- Negative stale-plan witness. -/
theorem stale_plan_rejected :
    accepts true snapshot stalePlan delta receipt = false := by
  decide

/-- Negative stale-receipt witness. -/
theorem stale_receipt_rejected :
    accepts true snapshot plan delta
      { receipt with sourceRevision := 6 } = false := by
  decide

def serializedReceipt : Receipt Backend Revision Observer PlanId DeltaId :=
  { receipt with mode := .serialized }

/-- Positive fallback witness: serialized evidence remains acceptable after a
backend declines parallel admission. -/
theorem serialized_fallback_accepted :
    accepts false snapshot plan delta serializedReceipt = true := by
  decide

/-- Negative fallback witness: a parallel receipt cannot claim an admission
that the backend declined. -/
theorem forged_parallel_after_decline_rejected :
    accepts false snapshot plan delta receipt = false := by
  decide

private def retarget (backend : Backend) (revision : Revision)
    (occurrence : OccurrenceId Backend Revision) :
    OccurrenceId Backend Revision :=
  ⟨⟨backend, revision⟩, occurrence.logicalIndex⟩

private def serialDelta
    (current : Snapshot Backend Revision Payload)
    (operator : OperatorPlan Backend Revision Observer PlanId) :
    Delta Backend Revision Payload DeltaId where
  id := operator.id
  sourceBackend := operator.sourceBackend
  targetBackend := operator.targetBackend
  sourceRevision := operator.sourceRevision
  targetRevision := current.revision + 1
  entries := operator.authoredOccurrences.map fun occurrence =>
    (retarget operator.targetBackend (current.revision + 1) occurrence, ())

private def serialReceipt
    (current : Snapshot Backend Revision Payload)
    (operator : OperatorPlan Backend Revision Observer PlanId) :
    Receipt Backend Revision Observer PlanId DeltaId where
  planId := operator.id
  observer := operator.observer
  sourceBackend := operator.sourceBackend
  targetBackend := operator.targetBackend
  sourceRevision := operator.sourceRevision
  targetRevision := current.revision + 1
  deltaId := operator.id
  mode := .serialized
  authoredOccurrences := operator.authoredOccurrences
  emittedOccurrences :=
    (serialDelta current operator).entries.map Prod.fst

private def serialRun
    (current : Snapshot Backend Revision Payload)
    (operator : OperatorPlan Backend Revision Observer PlanId) :
    Option (Delta Backend Revision Payload DeltaId ×
      Receipt Backend Revision Observer PlanId DeltaId) :=
  if current.wellScoped operator then
    some (serialDelta current operator, serialReceipt current operator)
  else
    none

private theorem serial_result_accepted
    (current : Snapshot Backend Revision Payload)
    (operator : OperatorPlan Backend Revision Observer PlanId)
    (isScoped : current.wellScoped operator = true) :
    accepts false current operator (serialDelta current operator)
      (serialReceipt current operator) = true := by
  have sourceRevision : operator.sourceRevision = current.revision := by
    have conditions := isScoped
    simp [Snapshot.wellScoped] at conditions
    exact conditions.1.2.symm
  simp [accepts, isScoped, sourceRevision, Delta.wellScoped,
    serialDelta, serialReceipt,
    identityAligned, occurrenceEvidenceAligned, modeAllowed, retarget]

/-- A backend that admits no parallel plans still satisfies the realization
principles by executing every well-scoped plan serially. -/
def serialOnlyRealization :
    ExecutableRealization Backend Revision Payload Observer PlanId DeltaId
      (fun _ _ => False) where
  parallelAdmitted := fun _ _ => false
  parallelSound := by simp
  run := serialRun
  sound := by
    intro current operator produced evidence ran
    simp only [serialRun] at ran
    split at ran
    · rename_i isScoped
      simp only [Option.some.injEq, Prod.mk.injEq] at ran
      rcases ran with ⟨rfl, rfl⟩
      exact serial_result_accepted current operator isScoped
    · simp at ran
  rejectsIllScoped := by
    intro current operator invalid
    simp [serialRun, invalid]
  serializesDeclined := by
    intro current operator isScoped _
    exact ⟨serialDelta current operator, serialReceipt current operator,
      by simp [serialRun, isScoped], rfl⟩

/-- Positive behavior witness for the serialization obligation itself. -/
theorem declined_plan_really_runs_serially :
    ∃ produced evidence,
      serialOnlyRealization.run snapshot plan = some (produced, evidence) ∧
      evidence.mode = .serialized :=
  serialOnlyRealization.serializesDeclined snapshot plan (by decide) rfl

def returnOccurrence (index : Nat) : OccurrenceId Backend Revision :=
  ⟨⟨.native, 9⟩, index⟩

def pathMapSnapshot : Snapshot Backend Revision Payload :=
  ⟨.pathMap, 8, [(), ()]⟩

def returnPlan : OperatorPlan Backend Revision Observer PlanId where
  id := 18
  observer := true
  sourceBackend := .pathMap
  targetBackend := .native
  sourceRevision := 8
  authoredOccurrences :=
    [pathMapSnapshot.occurrenceId 0, pathMapSnapshot.occurrenceId 1]

def returnDelta : Delta Backend Revision Payload DeltaId where
  id := 24
  sourceBackend := .pathMap
  targetBackend := .native
  sourceRevision := 8
  targetRevision := 9
  entries := [(returnOccurrence 0, ()), (returnOccurrence 1, ())]

def returnReceipt : Receipt Backend Revision Observer PlanId DeltaId where
  planId := 18
  observer := true
  sourceBackend := .pathMap
  targetBackend := .native
  sourceRevision := 8
  targetRevision := 9
  deltaId := 24
  mode := .serialized
  authoredOccurrences := [targetOccurrence 0, targetOccurrence 1]
  emittedOccurrences := [returnOccurrence 0, returnOccurrence 1]

def nativeToPathMap :
    TransferLeg Backend Revision Payload Observer PlanId DeltaId :=
  TransferLeg.ofAccepted true snapshot plan delta receipt
    ordered_duplicates_accepted

theorem return_execution_accepted :
    accepts false pathMapSnapshot returnPlan returnDelta returnReceipt = true := by
  decide

def pathMapToNative :
    TransferLeg Backend Revision Payload Observer PlanId DeltaId :=
  TransferLeg.ofAccepted false pathMapSnapshot returnPlan returnDelta
    returnReceipt return_execution_accepted

def outbound :
    TransferTrace Backend Revision Payload Observer PlanId DeltaId :=
  TransferTrace.singleton nativeToPathMap

def inbound :
    TransferTrace Backend Revision Payload Observer PlanId DeltaId :=
  TransferTrace.singleton pathMapToNative

/-- Positive heterogeneous-composition witness: native to PathMap to native
composes and retains both deltas and both receipts in order. -/
theorem native_pathMap_native_composes :
    ∃ trace,
      TransferTrace.compose? outbound inbound = some trace ∧
      trace.legs = [nativeToPathMap, pathMapToNative] := by
  exact ⟨⟨nativeToPathMap, [pathMapToNative]⟩, rfl, rfl⟩

def staleInbound :
    TransferTrace Backend Revision Payload Observer PlanId DeltaId :=
  TransferTrace.singleton
    ⟨{ returnDelta with sourceRevision := 7 },
      { returnReceipt with sourceRevision := 7 }⟩

/-- Negative heterogeneous-composition witness: a mismatched middle revision
is rejected rather than silently rebased. -/
theorem stale_middle_revision_rejected :
    TransferTrace.compose? outbound staleInbound = none := by
  decide

end Example

end Mettapedia.GSLT.Dynamics.OperatorRealization
