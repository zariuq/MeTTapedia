import Mettapedia.GSLT.LanguageDef.OperationCostProtocol
import Mettapedia.Machines.ResumableRegion
import Mettapedia.Machines.Cursor.Fold
import Mettapedia.Machines.SourceProducerCardinality.Controls
import Mettapedia.Machines.ErrorBoundaryContracts.DispatchPermit

/-! Executable positive and negative controls for the native-invoice cursor.
These use state changes, failures, suspension and unbounded zero-work stepping;
none treat a finite inspection allowance as a termination proof. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OperationCostProtocolControls

open Mettapedia.GSLT.LanguageDef.OperationCostProtocol
open Mettapedia.GSLT.LanguageDef.OperationCostProtocol.NativePoll
open Mettapedia.GSLT.LanguageDef.OperationContracts
open Mettapedia.GSLT.LanguageDef.MacroExportPlan (Atom)
open Mettapedia.Machines
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.SeparationTransport

def sampleRecord (progress replay : String) (bound : Atom) (kinds : List Atom) : Atom :=
  .list [.symbol "cesta-operation-protocol/1", .symbol "sample",
    .list (.symbol "ChargeKinds" :: kinds),
    .list [.symbol "Progress", .text progress, .list [.symbol "Bound", bound]],
    .list [.symbol "Replay", .text replay]]

theorem source_record_admitted : admitted
    (exampleOperation "sample" "sample" (footprintAtom [] []) "yes" "no")
    (sampleRecord "single" "refused" (.symbol "1") []) = true := by decide

theorem single_bound_cannot_be_unknown : admitted
    (exampleOperation "sample" "sample" (footprintAtom [] []) "yes" "no")
    (sampleRecord "single" "refused" (.text "unknown") []) = false := by decide

theorem source_labels_must_match : admitted
    (exampleOperation "sample" "sample" (footprintAtom [] []) "yes" "no")
    (sampleRecord "single" "refused" (.symbol "1")
      [.list [.symbol "not-declared", .symbol "analysisStep"]]) = false := by decide

theorem source_progress_must_match : admitted
    (exampleOperation "sample" "sample" (footprintAtom [] []) "yes" "no")
    (sampleRecord "steps" "refused" (.text "unknown") []) = false := by decide

theorem source_replay_must_match : admitted
    (exampleOperation "sample" "sample" (footprintAtom [] []) "yes" "no")
    (sampleRecord "single" "transparent" (.symbol "1") []) = false := by decide

def metered : Profile :=
  ⟨"sample", [("step", some .analysisStep)], .steps, none, .transparent⟩

def receipt (identity units : Nat) : Event :=
  (identity, ⟨0, identity, .analysisStep, units⟩)

def bounded : Profile :=
  ⟨"bounded-slot", [("work", some .analysisStep)], .bounded, some 3, .refused⟩

def yielding : Profile :=
  ⟨"yielding-slot", [("work", some .analysisStep)], .steps, none, .refused⟩

def completeReceipt : SlotReceipt :=
  [(.admission, receipt 0 1), (.preparation, receipt 1 1),
    (.execution, receipt 2 1), (.delivery, receipt 3 1),
    (.teardown, receipt 4 1), (.arrivals, receipt 5 1),
    (.bookkeeping, receipt 6 1)]

def orderedPollA : NativePoll.Receipt :=
  ⟨false, .paused,
    [(.sourceWork, receipt 20 1), (.sourceWork, receipt 21 2)]⟩

def orderedPollB : NativePoll.Receipt :=
  ⟨false, .paused,
    [(.sourceWork, receipt 21 2), (.sourceWork, receipt 20 1)]⟩

def orderedPollCoalesced : NativePoll.Receipt :=
  ⟨false, .paused, [(.sourceWork, receipt 22 3)]⟩

def producerTaggedPoll : NativePoll.Receipt :=
  ⟨false, .paused, [(.producer, receipt 23 2)]⟩

def sourceTaggedPoll : NativePoll.Receipt :=
  ⟨false, .paused, [(.sourceWork, receipt 23 2)]⟩

/-- Positive control: the ordered schema retains both native event order and
physical identities through erasure to the generic slot receipt. -/
theorem ordered_poll_erasure_preserves_occurrences :
    slotInvoice (toSlotReceipt orderedPollA) = [receipt 20 1, receipt 21 2] ∧
      orderedView orderedPollA ≠ orderedView orderedPollB := by decide

/-- Negative control: the aggregate forgets order even when the exact same
physical occurrences are merely reversed. -/
theorem aggregate_forgets_occurrence_order :
    orderedPollA ≠ orderedPollB ∧
      summarize orderedPollA = summarize orderedPollB ∧
      toSlotReceipt orderedPollA ≠ toSlotReceipt orderedPollB := by decide

/-- It also forgets how total work was partitioned into physical occurrences. -/
theorem aggregate_forgets_occurrence_partition :
    orderedPollA ≠ orderedPollCoalesced ∧
      summarize orderedPollA = summarize orderedPollCoalesced := by decide

/-- The generic slot erasure is intentionally too coarse to recover native
poll call structure: producer and source-work tags both become execution. -/
theorem generic_slot_erasure_forgets_poll_tag :
    producerTaggedPoll ≠ sourceTaggedPoll ∧
      toSlotReceipt producerTaggedPoll = toSlotReceipt sourceTaggedPoll ∧
      summarize producerTaggedPoll ≠ summarize sourceTaggedPoll := by decide

theorem aggregate_projection_not_injective : ¬ Function.Injective summarize := by
  intro injective
  exact aggregate_forgets_occurrence_order.1
    (injective aggregate_forgets_occurrence_order.2.1)

/-- No function can reconstruct every ordered poll receipt from the aggregate
alone.  Additional native ordering evidence is mathematically necessary. -/
theorem no_aggregate_reconstruction :
    ¬ ∃ reconstruct : Aggregate → NativePoll.Receipt,
      Function.LeftInverse reconstruct summarize := by
  rintro ⟨reconstruct, leftInverse⟩
  exact aggregate_projection_not_injective leftInverse.injective

def admissionPoll : NativePoll.Receipt :=
  ⟨true, .complete,
    [(.admission .ready, receipt 30 0), (.consumer, receipt 31 0),
      (.transport, receipt 32 3), (.finalCurrent, receipt 33 0),
      (.retirement, receipt 34 0)]⟩

/-- Positive projection control: last admission, callback counts and exposed
transport delta are read from one ordered receipt without assuming a hidden
canonical order. -/
theorem admission_poll_projects_exact_aggregate :
    summarize admissionPoll =
      { initialPending := true
        step := .complete
        lastAdmission := some .ready
        admissionCalls := 1
        consumerCalls := 1
        finalCurrentCalls := 1
        retirements := 1
        transportWork := 3 } := by decide

/-! The live indexed-row control supplies a genuinely ready retained
invocation.  These controls join it to current indexed authority, validated
publication and the ordered poll-history boundary without defining another
machine. -/

namespace CurrentPublicationControls

open Mettapedia.Machines.Cursor.Fold.OwnedSequence.CallbackBoundary.FrozenPublication.CheckedPreparation.IndexedService.Controls
open OperationCostProtocol.Indexed

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

local instance publicationDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority
      (Access.consume : revocationWorlds.Fibre point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true →
      Access.separate Access.consume frame = true))

def invocationPoll : NativePoll.Receipt :=
  ⟨false, .complete,
    retainedInvocation.account.events.map fun event => (.sourceWork, event)⟩

def invocationHistory : NativePoll.History := [invocationPoll]

theorem invocation_history_covers_paid_account :
    OperationCostProtocol.Indexed.Invocation.PollHistoryCovers
      (source := machine) (gate := phaseGate) (profiles := phaseProfiles)
      (replay := phaseReplay) (invoice := phaseInvoice) (reader := program)
      (notice := continuous) retainedInvocation invocationHistory := by
  simp [OperationCostProtocol.Indexed.Invocation.PollHistoryCovers,
    invocationHistory, invocationPoll, NativePoll.historyEvents,
    NativePoll.receiptEvents]

def currentPoint : IndexedAuthority.Point revocationWorlds := ⟨false, .consume⟩
def revokedPoint : IndexedAuthority.Point revocationWorlds := ⟨true, .none⟩

open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone (Handle)

def issuedGrantHandle : Handle Unit (Nat × Nat) := ⟨(), (7, 1001), 1⟩
def regrantedHandle : Handle Unit (Nat × Nat) := ⟨(), (7, 1001), 3⟩

def retainedGrant : CheckedGrant.Requirement Unit (Nat × Nat) Access :=
  ⟨issuedGrantHandle, .consume⟩

def issuedGrantView : CheckedGrant.View Unit (Nat × Nat) Access :=
  ⟨issuedGrantHandle, .consume⟩

def regrantedView : CheckedGrant.View Unit (Nat × Nat) Access :=
  ⟨regrantedHandle, .consume⟩

def revokedGrantView : CheckedGrant.View Unit (Nat × Nat) Access :=
  ⟨issuedGrantHandle, .none⟩

/-- Positive: a retained requirement is current at the exact issued generation
when the live authority still supplies its required frame. -/
theorem issued_generation_is_current : retainedGrant.Current issuedGrantView := by
  exact ⟨rfl, FrameUpdate.refl _⟩

/-- Negative: restoring the same rights at a new generation does not revive an
old retained requirement. -/
theorem revoke_then_regrant_does_not_revive_old_generation :
    ¬ retainedGrant.Current regrantedView := by
  apply CheckedGrant.Requirement.not_current_of_generation_ne
  decide

def accessPermission (current required : Access) : Decidable (FrameUpdate current required) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate current frame = true → Access.separate required frame = true))

def cachedGrantDecision : CheckedDecision.Decision Unit (Nat × Nat) Access String :=
  ⟨retainedGrant, some "appended"⟩

def retiredGrantDecision : CheckedDecision.Decision Unit (Nat × Nat) Access String :=
  ⟨retainedGrant, none⟩

/-- A current full receipt returns its cached reply without execution. -/
theorem current_cached_decision_returns_reply :
    CheckedDecision.retry accessPermission issuedGrantView (some cachedGrantDecision) =
      .cached "appended" := by
  rfl

/-- Evicting the full reply retains the durable decision and yields explicit
unknown rather than re-entering execution. -/
theorem retired_decision_is_unknown_not_execute :
    CheckedDecision.retry accessPermission issuedGrantView (some retiredGrantDecision) =
      .unknown := by
  rfl

/-- Equal rights at a fresh generation cannot observe an old cached result. -/
theorem regranted_generation_refuses_cached_decision :
    CheckedDecision.retry accessPermission regrantedView (some cachedGrantDecision) =
      .refused := by
  rfl

/-- Revoking the required right refuses a cached result even while the
generation-bearing handle itself is unchanged. -/
theorem revoked_authority_refuses_cached_decision :
    CheckedDecision.retry accessPermission revokedGrantView (some cachedGrantDecision) =
      .refused := by
  rfl

/-- Only a genuinely absent decision licenses a first execution. -/
theorem missing_decision_executes :
    CheckedDecision.retry accessPermission issuedGrantView
      (none : Option (CheckedDecision.Decision Unit (Nat × Nat) Access String)) = .execute := by
  rfl

def publishAt (point : IndexedAuthority.Point revocationWorlds) (current : Nat → Nat) :=
  OperationCostProtocol.Indexed.Invocation.publishCurrent
    (source := machine) (gate := phaseGate) (profiles := phaseProfiles)
    (replay := phaseReplay) (invoice := phaseInvoice) (reader := program)
    (notice := continuous)
    (fun {index} result => publicationWrites (_index := index) result)
    retainedInvocation retained_invocation_is_ready invocationHistory
    revocationWorlds point Access.consume "denied" current

def publishWithGrant (handle : Handle Unit (Nat × Nat)) (current : Nat → Nat) :=
  letI : Decidable (FrameUpdate currentPoint.authority retainedGrant.required) :=
    publicationDecision currentPoint
  OperationCostProtocol.Indexed.Invocation.publishCheckedGrant
      (source := machine) (gate := phaseGate) (profiles := phaseProfiles)
      (replay := phaseReplay) (invoice := phaseInvoice) (reader := program)
      (notice := continuous)
      (fun {index} result => publicationWrites (_index := index) result)
      retainedInvocation retained_invocation_is_ready invocationHistory
      revocationWorlds currentPoint retainedGrant handle "denied" current

/-- The exact current grant reaches the existing current-authority and
dependency-validated publication path. -/
theorem current_generation_publishes_validated_state :
    publishWithGrant issuedGrantHandle publicationSnapshot =
      .committed (ValidatedCommit.write publicationSnapshot [(1, 18)]) invocationHistory := by
  rfl

/-- Even with restored consume rights and unchanged data, a new grant
generation returns the exact paid residual and history instead of publishing. -/
theorem stale_generation_returns_exact_retry_residual :
    publishWithGrant regrantedHandle publicationSnapshot =
      .authorityRefused "denied" retainedInvocation invocationHistory := by
  rfl

/-- Positive: current consume authority and the exact retained manifest publish
the ready invocation.  The poll history crosses the boundary unchanged. -/
theorem current_authority_publishes_validated_state :
    publishAt currentPoint publicationSnapshot =
      .committed (ValidatedCommit.write publicationSnapshot [(1, 18)]) invocationHistory := by
  rfl

/-- Authority is checked first.  Revocation wins even when the dependency
store is also stale, and both the invocation and ordered history are returned
for policy replacement or inspection. -/
theorem authority_refusal_precedes_dependency_conflict :
    publishAt revokedPoint changedPublicationStore =
      .authorityRefused "denied" retainedInvocation invocationHistory := by
  rfl

/-- With current authority, changing the recorded dependency is a separate
conflict and returns the same paid residual and history. -/
theorem changed_dependency_returns_exact_retry_residual :
    publishAt currentPoint changedPublicationStore =
      .dependencyConflict retainedInvocation invocationHistory := by
  rfl

def unrelatedStore : Nat → Nat := Function.update publicationSnapshot 2 99

/-- A change outside the retained manifest does not manufacture a conflict. -/
theorem unrelated_change_still_publishes :
    publishAt currentPoint unrelatedStore =
      .committed (ValidatedCommit.write unrelatedStore [(1, 18)]) invocationHistory ∧
      (ValidatedCommit.write unrelatedStore [(1, 18)]) 0 = 7 ∧
      (ValidatedCommit.write unrelatedStore [(1, 18)]) 1 = 18 ∧
      (ValidatedCommit.write unrelatedStore [(1, 18)]) 2 = 99 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Publication does not execute or acknowledge the later outbox delivery
phase.  Its committed branch contains the validated state and prior poll
history only. -/
theorem committed_publication_is_not_a_delivery_result :
    (match publishAt currentPoint publicationSnapshot with
      | .committed _ history => history = invocationHistory
      | .authorityRefused _ _ _ | .dependencyConflict _ _ => false) := by
  rfl

def deliveryAttemptPoll : NativePoll.Receipt :=
  ⟨false, .complete, [(.transport, receipt 40 1)]⟩

def deliveryReceiptPoll : NativePoll.Receipt :=
  ⟨false, .complete, [(.transport, receipt 41 0)]⟩

def deliveryRetryPoll : NativePoll.Receipt :=
  ⟨false, .complete, [(.transport, receipt 42 1)]⟩

def pendingDelivery : DeliveryRecovery.State String String :=
  ⟨["task-1"], [], []⟩

def missingDelivery : DeliveryRecovery.State String String :=
  ⟨[], [], []⟩

def lostAckResult : DeliveryRecovery.Result String String :=
  DeliveryRecovery.attempt .idempotentByKey false pendingDelivery
    invocationHistory deliveryAttemptPoll "task-1" "bytes-v1"

def recoveredLostAck : DeliveryRecovery.Result String String :=
  DeliveryRecovery.recover .idempotentByKey lostAckResult
    deliveryReceiptPoll "task-1"

/-- The delivery handler starts after publication and receives the publication
history unchanged.  Neither refusal branch can enter this later phase. -/
theorem only_committed_publication_enters_delivery :
    OperationCostProtocol.Indexed.Invocation.PublicationResult.deliver
        (source := machine) (gate := phaseGate) (profiles := phaseProfiles)
        (replay := phaseReplay) (invoice := phaseInvoice) (reader := program)
        (notice := continuous)
        (publishAt currentPoint publicationSnapshot) .idempotentByKey false
          pendingDelivery deliveryAttemptPoll "task-1" "bytes-v1" = some lostAckResult ∧
      OperationCostProtocol.Indexed.Invocation.PublicationResult.deliver
        (source := machine) (gate := phaseGate) (profiles := phaseProfiles)
        (replay := phaseReplay) (invoice := phaseInvoice) (reader := program)
        (notice := continuous)
        (publishAt revokedPoint changedPublicationStore) .idempotentByKey false
          pendingDelivery deliveryAttemptPoll "task-1" "bytes-v1" = none ∧
      OperationCostProtocol.Indexed.Invocation.PublicationResult.deliver
        (source := machine) (gate := phaseGate) (profiles := phaseProfiles)
        (replay := phaseReplay) (invoice := phaseInvoice) (reader := program)
        (notice := continuous)
        (publishAt currentPoint changedPublicationStore) .idempotentByKey false
          pendingDelivery deliveryAttemptPoll "task-1" "bytes-v1" = none := by
  exact ⟨rfl, rfl, rfl⟩

/-- A durable RESULT can commit while its reply is lost.  The client first
sees `unknown`; a later RECEIPT sees the retained result as `stored`.  Both
steps retain their exact ordered receipts, and the physical effect occurs
once. -/
theorem lost_ack_receipt_recovers_one_durable_effect :
    lostAckResult.status = .unknown ∧
      lostAckResult.state.records = [("task-1", "bytes-v1")] ∧
      lostAckResult.state.effects = [("task-1", "bytes-v1")] ∧
      lostAckResult.history = invocationHistory ++ [deliveryAttemptPoll] ∧
      recoveredLostAck.status = .stored ∧
      recoveredLostAck.state = lostAckResult.state ∧
      recoveredLostAck.state.effects = [("task-1", "bytes-v1")] ∧
      recoveredLostAck.history =
        invocationHistory ++ [deliveryAttemptPoll, deliveryReceiptPoll] := by
  decide

def changedPayloadResult : DeliveryRecovery.Result String String :=
  DeliveryRecovery.attempt .idempotentByKey true lostAckResult.state
    lostAckResult.history deliveryRetryPoll "task-1" "bytes-v2"

/-- A stable key cannot be reused for different bytes.  Conflict leaves both
the durable result and the one physical effect unchanged. -/
theorem changed_payload_at_same_key_conflicts :
    changedPayloadResult.status = .conflict ∧
      changedPayloadResult.state = lostAckResult.state ∧
      changedPayloadResult.state.effects = [("task-1", "bytes-v1")] ∧
      changedPayloadResult.history =
        invocationHistory ++ [deliveryAttemptPoll, deliveryRetryPoll] := by
  decide

def pendingReceiptResult : DeliveryRecovery.Result String String :=
  DeliveryRecovery.queryReceipt pendingDelivery invocationHistory
    deliveryReceiptPoll "task-1"

def missingReceiptResult : DeliveryRecovery.Result String String :=
  DeliveryRecovery.queryReceipt missingDelivery invocationHistory
    deliveryReceiptPoll "task-1"

/-- Receipt inspection distinguishes a task that still exists from a missing
key.  Missing is reported honestly as `unknown`, never as `stored`. -/
theorem receipt_distinguishes_pending_from_missing :
    pendingReceiptResult.status = .pending ∧
      missingReceiptResult.status = .unknown ∧
      missingReceiptResult.state.records = [] ∧
      missingReceiptResult.state.effects = [] ∧
      missingReceiptResult.history = invocationHistory ++ [deliveryReceiptPoll] := by
  decide

def uncertainResult : DeliveryRecovery.Result String String :=
  DeliveryRecovery.attempt .explicitUnknown false pendingDelivery
    invocationHistory deliveryAttemptPoll "task-1" "external-effect"

def heldUncertain : DeliveryRecovery.Result String String :=
  DeliveryRecovery.recover .explicitUnknown uncertainResult
    deliveryReceiptPoll "task-1"

/-- An unqueryable lost acknowledgment remains explicitly uncertain.  The
recovery policy preserves state and history exactly and performs no replay. -/
theorem explicit_unknown_recovery_is_inert :
    uncertainResult.status = .unknown ∧
      uncertainResult.state.pending = ["task-1"] ∧
      uncertainResult.state.effects = [("task-1", "external-effect")] ∧
      uncertainResult.history = invocationHistory ++ [deliveryAttemptPoll] ∧
      heldUncertain = uncertainResult := by
  decide

def manuallyReplayedUncertain : DeliveryRecovery.Result String String :=
  DeliveryRecovery.attempt .explicitUnknown true uncertainResult.state
    uncertainResult.history deliveryRetryPoll "task-1" "external-effect"

/-- Negative control: overriding the policy and directly replaying an effect
whose result cannot be queried can execute it twice.  An acknowledgment of the
second attempt is not durable-ledger evidence. -/
theorem direct_non_idempotent_replay_can_duplicate :
    manuallyReplayedUncertain.status = .acknowledged ∧
      manuallyReplayedUncertain.state.records = [] ∧
      manuallyReplayedUncertain.state.effects =
        [("task-1", "external-effect"), ("task-1", "external-effect")] ∧
      manuallyReplayedUncertain.history =
        invocationHistory ++ [deliveryAttemptPoll, deliveryRetryPoll] := by
  decide

end CurrentPublicationControls

namespace HandlerSubstitutionControls

open Mettapedia.Machines.Cursor.Fold.OwnedSequence.CallbackBoundary.FrozenPublication.CheckedPreparation.IndexedService.Controls
open OperationCostProtocol.Indexed
open Mettapedia.TypeTheory Mettapedia.TypeTheory.IndexedPolynomial

/-- The second handler stores the revision first, then the physical event
counter, authority, semantic step counter and the two mutation switches. -/
abbrev TuplePrivate := Nat × Nat × Access × Nat × Bool × Bool

def encode (state : Private) : TuplePrivate :=
  (state.revision, state.nextEvent, state.right, state.steps, state.revokeAfter, state.changeAfter)

def tupleMachine : Cursor.Provider phases where
  State _ _ := TuplePrivate
  step := fun {_} {index} state row => match state with
    | (revision, event, right, steps, revoke, changed) => match index with
      | none => ⟨row.payload + row.environment + 100 * steps,
          (if changed then 8 else revision, event + 1,
            if revoke then .read else right, steps + 1, revoke, changed)⟩
      | some value => ⟨decide (value ≠ 99), (revision, event + 1, right, steps + 1, revoke, changed)⟩

def representation : Cursor.Hom machine tupleMachine where
  map state := encode state
  step := by
    intro base index state row
    cases index <;> rfl

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority
      (Access.consume : revocationWorlds.Fibre point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true →
      Access.separate Access.consume frame = true))

def tupleGate : Gate (Denied := String) tupleMachine := fun state _ =>
  match state with
  | (revision, _, right, _, _, _) =>
      let point : IndexedAuthority.Point revocationWorlds := ⟨false, right⟩
      letI : Decidable (FrameUpdate point.authority
          (Access.consume : revocationWorlds.Fibre point.world)) := permissionDecision point
      currentGate revocationWorlds point Access.consume
        (fun _ : Unit => revision) [((), 7)] "denied" "changed"

def tupleInvoice : Invoice tupleMachine := fun {_} {index} state row =>
  [(state.2.1, ⟨row.environment, row.payload,
    if index.isNone then .heapLookup else .analysisStep, if index.isNone then 3 else 5⟩)]

def substitution : HandlerHom machine tupleMachine phaseGate tupleGate
    phaseProfiles phaseProfiles phaseReplay phaseReplay phaseInvoice tupleInvoice where
  representation := representation
  gate_eq _ _ := rfl
  profiles_eq _ := rfl
  replay_eq _ := rfl
  invoice_eq _ _ := rfl

def decode : TuplePrivate → Private
  | (revision, event, right, steps, revoke, changed) =>
      ⟨steps, event, right, revision, revoke, changed⟩

def reverseRepresentation : Cursor.Hom tupleMachine machine where
  map := decode
  step := by
    intro base index state row
    rcases state with ⟨revision, event, right, steps, revoke, changed⟩
    cases index <;> rfl

def reverseSubstitution : HandlerHom tupleMachine machine tupleGate phaseGate
    phaseProfiles phaseProfiles phaseReplay phaseReplay tupleInvoice phaseInvoice where
  representation := reverseRepresentation
  gate_eq state _ := by rcases state with ⟨revision, event, right, steps, revoke, changed⟩; rfl
  profiles_eq _ := rfl
  replay_eq _ := rfl
  invoice_eq _ _ := rfl

/-- A genuine round trip passes through the tuple representation and recovers
all six source fields, including authority and invalidation switches. -/
theorem composed_substitution_recovers_source_state (state : Private) :
    (substitution.comp reverseSubstitution).representation.map
      (base := ()) (index := none) state = state := rfl

def start (right : Access) (notice : Notice phases String) :
    Cursor.Packet (provider machine phaseGate phaseProfiles phaseReplay phaseInvoice)
      (client program notice) () :=
  ⟨none, .inl (first, none), (⟨0, 0, right, 7, false, false⟩, initial phaseProfile 100)⟩

structure TupleView where
  finished : Bool
  phase : Option Nat
  ready : Option (Except Unit Row)
  refusal : Option (Reason String)
  pending : Option Row
  physical : TuplePrivate
  account : Account
  deriving DecidableEq, Repr

def view {gate : Gate (Denied := String) tupleMachine} {invoice : Invoice tupleMachine}
    {notice : Notice phases String} :
    Outcome tupleMachine gate phaseProfiles phaseReplay invoice program notice () → TupleView
  | .paused ⟨index, .inl (row, _), state⟩ =>
      ⟨false, index, none, none, some row, state.1, state.2⟩
  | .paused ⟨index, .inr (reason, row, _), state⟩ =>
      ⟨false, index, none, some reason, some row, state.1, state.2⟩
  | .done ⟨index, .inl result, state⟩ =>
      ⟨true, index, some result, none, none, state.1, state.2⟩
  | .done ⟨index, .inr (reason, row, _), state⟩ =>
      ⟨true, index, none, some reason, some row, state.1, state.2⟩

def targetRun (notice : Notice phases String) (fuel : Nat) (right : Access) :=
  Indexed.run tupleMachine tupleGate phaseProfiles phaseReplay tupleInvoice program notice fuel
    (substitution.lift.packet (client program notice) (start right notice))

/-- The target really executes both distinct reply phases in its tuple store;
it does not return a precomputed source outcome. -/
theorem different_representation_executes_both_phases :
    let result := targetRun continuous 3 .consume
    result.1 = 8 ∧
      view result.2 =
        ⟨true, some 18, some (.ok {first with payload := 18}), none, none,
          (7, 2, .consume, 2, false, false),
          ⟨92, none, 2,
            [(0, ⟨11, 7, .heapLookup, 3⟩), (1, ⟨11, 18, .analysisStep, 5⟩)]⟩⟩ := by
  decide

/-- A pre-call refusal holds the original root, tuple state and empty invoice. -/
theorem current_gate_refusal_retains_pending_root :
    let result := targetRun continuous 2 .read
    result.1 = 0 ∧
      view result.2 =
        ⟨true, none, none, some (.inl "denied"), some first,
          (7, 0, .read, 0, false, false), initial phaseProfile 100⟩ := by
  decide

/-- A post-reply refusal instead holds the selected phase and its paid first
invoice. It cannot be replaced by the original pending root. -/
theorem paid_reply_refusal_retains_selected_phase :
    let result := targetRun stopAfterMaterialization 2 .consume
    result.1 = 3 ∧
      view result.2 =
        ⟨true, some 18, none, some (.inl "partial"), some {first with payload := 18},
          (7, 1, .consume, 1, false, false),
          ⟨97, none, 1, [(0, ⟨11, 7, .heapLookup, 3⟩)]⟩⟩ := by
  decide

theorem both_refusals_can_be_scheduler_pauses :
    view (targetRun continuous 1 .read).2 =
      ⟨false, none, none, some (.inl "denied"), some first,
        (7, 0, .read, 0, false, false), initial phaseProfile 100⟩ ∧
      view (targetRun stopAfterMaterialization 1 .consume).2 =
        ⟨false, some 18, none, some (.inl "partial"), some {first with payload := 18},
          (7, 1, .consume, 1, false, false),
          ⟨97, none, 1, [(0, ⟨11, 7, .heapLookup, 3⟩)]⟩⟩ := by
  decide

theorem paid_retry_executes_only_selected_suffix :
    let previous := targetRun stopAfterMaterialization 2 .consume
    let result := Indexed.resume tupleMachine tupleGate phaseProfiles phaseReplay tupleInvoice
      program stopAfterMaterialization 2
      (previous.1, retry tupleMachine tupleGate phaseProfiles phaseReplay tupleInvoice
        program stopAfterMaterialization previous.2)
    result.1 = 8 ∧ (view result.2).ready = some (.ok {first with payload := 18}) ∧
      (view result.2).physical = (7, 2, .consume, 2, false, false) ∧
      (view result.2).account.remaining = 92 ∧ (view result.2).account.calls = 2 := by
  decide

/-- This instantiates the general run law on both refusal observations,
including every finite scheduler cut, not only the completed controls above. -/
theorem both_refusal_families_transport (fuel : Nat) (right : Access)
    (notice : Notice phases String) :
    ((Indexed.run machine phaseGate phaseProfiles phaseReplay phaseInvoice program notice
      fuel (start right notice)).1,
      substitution.mapOutcome program notice
        (Indexed.run machine phaseGate phaseProfiles phaseReplay phaseInvoice program notice
          fuel (start right notice)).2) = targetRun notice fuel right :=
  substitution.run program notice fuel (start right notice)

def heldTarget := substitution.invocation program continuous retainedInvocation

theorem submission_reads_account_and_history_survive :
    heldTarget.submission = retainedInvocation.submission ∧
      heldTarget.reads = retainedInvocation.reads ∧
      heldTarget.account = retainedInvocation.account ∧
      Invocation.PollHistoryCovers (source := tupleMachine) (gate := tupleGate)
        (profiles := phaseProfiles) (replay := phaseReplay) (invoice := tupleInvoice)
        (reader := program) (notice := continuous) heldTarget
        CurrentPublicationControls.invocationHistory := by
  refine ⟨rfl, rfl, substitution.invocation_account program continuous retainedInvocation, ?_⟩
  exact (substitution.invocation_history_iff program continuous retainedInvocation _).mpr
    CurrentPublicationControls.invocation_history_covers_paid_account

def deniedInvocation : Invocation (Key := Nat) (Value := Nat)
    machine phaseGate phaseProfiles phaseReplay phaseInvoice program continuous () :=
  let result := Indexed.run machine phaseGate phaseProfiles phaseReplay phaseInvoice program continuous
    2 (start .read continuous)
  ⟨retainedInvocation.submission, result.1, result.2⟩

/-- The current authority source may change independently of retained private
state.  Both replacement gates supply consume authority while retaining the
same dependency-revision check. -/
def restoredSourceGate : Gate (Denied := String) machine := fun state row =>
  phaseGate {state with right := .consume} row

def restoredTargetGate : Gate (Denied := String) tupleMachine := fun state row =>
  match state with
  | (revision, event, _, steps, revoke, changed) =>
      tupleGate (revision, event, .consume, steps, revoke, changed) row

theorem restored_gates_agree {base : Unit} {index : Option Nat}
    (state : machine.State base index) (row : phases.Shape base index) :
    restoredSourceGate state row = restoredTargetGate (representation.map state) row := rfl

def restoredTarget :=
  (substitution.invocation program continuous deniedInvocation).resumeWith
    tupleMachine tupleGate phaseProfiles phaseReplay tupleInvoice program continuous restoredTargetGate 3

theorem current_gate_installation_and_retry_transport :
    (substitution.withGates restoredSourceGate restoredTargetGate restored_gates_agree).invocation
      program continuous
      (deniedInvocation.resumeWith machine phaseGate phaseProfiles phaseReplay phaseInvoice
        program continuous restoredSourceGate 3) = restoredTarget :=
  substitution.invocation_resumeWith program continuous
    restoredSourceGate restoredTargetGate restored_gates_agree 3 deniedInvocation

theorem restored_authority_retries_original_phase_once :
    restoredTarget.spent = 8 ∧ restoredTarget.account.remaining = 92 ∧
      restoredTarget.account.calls = 2 ∧
      (match restoredTarget.outcome with
        | .done ⟨some 18, .inl (.ok row), state⟩ =>
            row.payload = 18 ∧ state.1 = (7, 2, .read, 2, false, false)
        | _ => False) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def publishTargetAt (point : IndexedAuthority.Point revocationWorlds) (current : Nat → Nat) :=
  Invocation.publishCurrent tupleMachine tupleGate phaseProfiles phaseReplay tupleInvoice program continuous
    (fun {index} result => publicationWrites (_index := index) result) heldTarget
    (substitution.invocation_ready program continuous _ retainedInvocation retained_invocation_is_ready)
    CurrentPublicationControls.invocationHistory revocationWorlds point Access.consume "denied" current

theorem current_publication_transport (point : IndexedAuthority.Point revocationWorlds)
    (current : Nat → Nat) :
    substitution.publication program continuous (CurrentPublicationControls.publishAt point current) =
      publishTargetAt point current :=
  substitution.publishCurrent program continuous _ retainedInvocation retained_invocation_is_ready
    CurrentPublicationControls.invocationHistory revocationWorlds point Access.consume "denied" current

theorem target_publication_checks_current_authority_and_manifest :
    publishTargetAt CurrentPublicationControls.currentPoint publicationSnapshot =
      .committed (ValidatedCommit.write publicationSnapshot [(1, 18)])
        CurrentPublicationControls.invocationHistory ∧
      publishTargetAt CurrentPublicationControls.revokedPoint changedPublicationStore =
        .authorityRefused "denied" heldTarget CurrentPublicationControls.invocationHistory ∧
      publishTargetAt CurrentPublicationControls.currentPoint changedPublicationStore =
        .dependencyConflict heldTarget CurrentPublicationControls.invocationHistory := by
  exact ⟨rfl, rfl, rfl⟩

def publishTargetWithGrant (handle : ForeignCapabilityLightcone.Handle Unit (Nat × Nat)) :=
  letI : Decidable (FrameUpdate CurrentPublicationControls.currentPoint.authority
      CurrentPublicationControls.retainedGrant.required) :=
    permissionDecision CurrentPublicationControls.currentPoint
  Invocation.publishCheckedGrant tupleMachine tupleGate phaseProfiles phaseReplay tupleInvoice program continuous
    (fun {index} result => publicationWrites (_index := index) result) heldTarget
    (substitution.invocation_ready program continuous _ retainedInvocation retained_invocation_is_ready)
    CurrentPublicationControls.invocationHistory revocationWorlds CurrentPublicationControls.currentPoint
    CurrentPublicationControls.retainedGrant handle "denied" publicationSnapshot

theorem generation_checked_publication_transport
    (handle : ForeignCapabilityLightcone.Handle Unit (Nat × Nat)) :
    substitution.publication program continuous
      (CurrentPublicationControls.publishWithGrant handle publicationSnapshot) =
      publishTargetWithGrant handle := by
  let _ : Decidable (FrameUpdate CurrentPublicationControls.currentPoint.authority
      CurrentPublicationControls.retainedGrant.required) :=
    permissionDecision CurrentPublicationControls.currentPoint
  exact substitution.publishCheckedGrant program continuous _ retainedInvocation retained_invocation_is_ready
    CurrentPublicationControls.invocationHistory revocationWorlds CurrentPublicationControls.currentPoint
    CurrentPublicationControls.retainedGrant handle "denied" publicationSnapshot

/-- Restoring identical rights at a new generation cannot revive the retained
source requirement after its handler representation has changed. -/
theorem target_regrant_does_not_revive_stale_handle :
    publishTargetWithGrant CurrentPublicationControls.issuedGrantHandle =
      .committed (ValidatedCommit.write publicationSnapshot [(1, 18)])
        CurrentPublicationControls.invocationHistory ∧
      publishTargetWithGrant CurrentPublicationControls.regrantedHandle =
        .authorityRefused "denied" heldTarget CurrentPublicationControls.invocationHistory := by
  exact ⟨rfl, rfl⟩

def rejectingGate : Gate (Denied := String) tupleMachine := fun _ _ => .error "denied"

/-- The source step map alone cannot license a target that refuses a request
the current source gate permits, regardless of the proposed representation. -/
theorem changed_gate_has_no_handler_hom :
    ¬ Nonempty (HandlerHom machine tupleMachine phaseGate rejectingGate
      phaseProfiles phaseProfiles phaseReplay phaseReplay phaseInvoice tupleInvoice) := by
  rintro ⟨candidate⟩
  have agreement := candidate.gate_eq (base := ()) (index := none)
    ⟨0, 0, .consume, 7, false, false⟩ first
  change (Except.ok () : Except String Unit) = .error "denied" at agreement
  cases agreement

def permissiveGate : Gate (Denied := String) tupleMachine := fun _ _ => .ok ()

/-- A forward step map also cannot justify adding authority: this target
executes two interactions that the source's current gate refuses. -/
theorem permissive_gate_invents_unauthorized_execution :
    let result := Indexed.run tupleMachine permissiveGate phaseProfiles phaseReplay tupleInvoice
      program continuous 3
      (substitution.lift.packet (client program continuous) (start .read continuous))
    (targetRun continuous 2 .read).1 = 0 ∧ result.1 = 8 ∧
      (view result.2).ready = some (.ok {first with payload := 18}) := by
  decide

theorem permissive_gate_has_no_handler_hom :
    ¬ Nonempty (HandlerHom machine tupleMachine phaseGate permissiveGate
      phaseProfiles phaseProfiles phaseReplay phaseReplay phaseInvoice tupleInvoice) := by
  rintro ⟨candidate⟩
  have agreement := candidate.gate_eq (base := ()) (index := none)
    ⟨0, 0, .read, 7, false, false⟩ first
  change (Except.error "denied" : Except String Unit) = .ok () at agreement
  cases agreement

def shiftedInvoice : Invoice tupleMachine := fun state row =>
  (tupleInvoice state row).map fun event => (event.1 + 100, event.2)

/-- Equal total work is weaker than the exact occurrence invoice required by
handler substitution.  Renaming an occurrence breaks that local law. -/
theorem equal_work_does_not_supply_invoice_agreement :
    let state : Private := ⟨0, 0, .consume, 7, false, false⟩
    work (phaseInvoice (base := ()) (index := none) state first) =
      work (shiftedInvoice (base := ()) (index := none) (encode state) first) ∧
      phaseInvoice (base := ()) (index := none) state first ≠
        shiftedInvoice (base := ()) (index := none) (encode state) first := by
  decide

def shiftedRun :=
  Indexed.run tupleMachine tupleGate phaseProfiles phaseReplay shiftedInvoice program continuous 3
    (substitution.lift.packet (client program continuous) (start .consume continuous))

def shiftedInvocation : Invocation (Key := Nat) (Value := Nat)
    tupleMachine tupleGate phaseProfiles phaseReplay shiftedInvoice program continuous () :=
  ⟨retainedInvocation.submission, shiftedRun.1, shiftedRun.2⟩

/-- Same answer, paid total and remaining budget still do not establish the
native-history obligation: the changed occurrences are absent from the poll. -/
theorem changed_invoice_breaks_history_despite_equal_totals :
    (view shiftedRun.2).ready = (view (targetRun continuous 3 .consume).2).ready ∧
      shiftedInvocation.spent = heldTarget.spent ∧
      shiftedInvocation.account.remaining = heldTarget.account.remaining ∧
      shiftedInvocation.account.events ≠ heldTarget.account.events ∧
      ¬ Invocation.PollHistoryCovers (source := tupleMachine) (gate := tupleGate)
        (profiles := phaseProfiles) (replay := phaseReplay) (invoice := shiftedInvoice)
        (reader := program) (notice := continuous) shiftedInvocation
        CurrentPublicationControls.invocationHistory := by
  unfold Invocation.PollHistoryCovers
  decide

def reversedHistory : NativePoll.History :=
  [⟨false, .complete,
    heldTarget.account.events.reverse.map fun event => (.sourceWork, event)⟩]

/-- Even unchanged event identities and equal charged work cannot replace
the declared occurrence order by a reversed delivery history. -/
theorem reversed_history_does_not_cover_ordered_account :
    work (NativePoll.historyEvents reversedHistory) = work heldTarget.account.events ∧
      ¬ Invocation.PollHistoryCovers (source := tupleMachine) (gate := tupleGate)
        (profiles := phaseProfiles) (replay := phaseReplay) (invoice := tupleInvoice)
        (reader := program) (notice := continuous) heldTarget reversedHistory := by
  unfold Invocation.PollHistoryCovers
  decide

end HandlerSubstitutionControls

/-- Positive bounded control: every complete phase is present in the exact
receipt, its finite declaration is recognized, and the existing exact account
debits the whole slot once. -/
theorem bounded_complete_slot_account :
    progressAdvice bounded .local = .bounded 3 ∧
      (slotCharge completeReceipt).total = 7 ∧
      prepareSlot bounded false completeReceipt (initial bounded 7) =
        .ok ⟨0, some 2, 1, slotInvoice completeReceipt⟩ := by decide

def completeReceiptMeter : SlotReceiptMeter := fun _ _ _ => completeReceipt

/-- The concrete receipt, rather than the profile's inspection allowance,
supplies the whole-slot work bound to the maintained ready-queue theorem. -/
theorem bounded_receipt_discharges_whole_slot :
    ReadyQueue.ServiceCostBound (receiptServiceMeter completeReceiptMeter) 7 2
      (fun _ => true) (fun _ => []) ⟨1, [1]⟩ := by
  apply serviceCostBound_of_receipts completeReceiptMeter 7 2
  intro n before
  simp [completeReceiptMeter, completeReceipt, slotInvoice, work, receipt,
    NativeCostLedger.totals, NativeCostLedger.eventGrade]

/-- Positive yielding control: the metadata requires a yielding realization,
while the existing resumable machine returns the exact residual and actual
transition debit of this slice. -/
theorem yielding_slice_retains_residual :
    progressAdvice yielding .local = .yielding ∧
      MachineCore.runSlice MachineCore.MaintenanceControls.countdown 2
        (MachineCore.MaintenanceControls.countdown.load 3) =
          (MachineCore.MaintenanceControls.countdown.load 1, 2) := by
  constructor <;> rfl

/-- Isolation is an explicit handler boundary, including for an operation
whose local progress remains unresolved. -/
theorem unknown_progress_requires_resolution_or_isolation :
    progressAdvice ⟨"unknown", [], .unknown, none, .refused⟩ .local = .unresolved ∧
      progressAdvice ⟨"unknown", [], .unknown, none, .refused⟩ .isolated = .isolated := by
  decide

/-- Negative control: one ready-queue dispatch can carry more work than any
proposed bound.  Dispatch count alone cannot discharge whole-slot admission. -/
theorem one_dispatch_does_not_bound_work (bound : Nat) :
    ∃ meter : ReadyQueue.ServiceMeter Nat,
      (ReadyQueue.costedServiceRun meter 1 (fun _ => true) (fun _ => [])
        ⟨1, [1]⟩).1.1 = [1] ∧
      bound < (ReadyQueue.costedServiceRun meter 1 (fun _ => true) (fun _ => [])
        ⟨1, [1]⟩).2 := by
  refine ⟨fun _ _ _ => ⟨bound + 1, 0, 0⟩, rfl, ?_⟩
  change bound < bound + 1 + 0 + 0 + 0
  omega

/-- Unlimited selection leaves the finite debit path unused; finite zero
remains a distinct setting and refuses this positive-work receipt. -/
theorem unlimited_is_not_finite_zero :
    debitAllowance .unlimited (slotInvoice completeReceipt) = some .unlimited ∧
      debitAllowance (.finite 0) (slotInvoice completeReceipt) = none := by decide

def invoice (_ : Bool) (world : Nat) : List Event := [receipt world 2]

def tick (_ : Bool) (world : Nat) : Reply Nat String String × Nat := (.paid, world + 1)

def fail (_ : Bool) (world : Nat) : Reply Nat String String × Nat :=
  (.terminal (.fault "allocation"), world + 1)

def wait (_ : Bool) (world : Nat) : Reply Nat String String × Nat :=
  (.terminal (.suspended "worker-7"), world + 1)

def finish (_ : Bool) (world : Nat) : Reply Nat String String × Nat :=
  (.terminal (.done 42), world + 1)

/-- Reading an existing cursor outcome keeps scheduler suspension separate
from its four tagged terminal cases. -/
def snapshot {p : Profile} {bill : Bool → Nat → List Event}
    {action : Bool → Nat → Reply Nat String String × Nat} :
    Outcome p bill action →
      (Control Nat String String ⊕ Terminal Nat String String) × Nat × Account
  | .paused ⟨_, control, state⟩ => (.inl control, state)
  | .done ⟨_, result, state⟩ => (.inr result, state)

theorem insufficient_budget_no_action :
    let answer := run metered invoice tick 2
      ⟨PUnit.unit, .running false, 0, initial metered 1⟩
    answer.1 = 0 ∧ snapshot answer.2 =
      (.inr (.refused .budget), 0, initial metered 1) := by decide

theorem paid_failure_retains_cost_and_mutation :
    let answer := run metered invoice fail 2
      ⟨PUnit.unit, .running false, 0, initial metered 5⟩
    answer.1 = 2 ∧ snapshot answer.2 =
      (.inr (.fault "allocation"), 1, ⟨3, none, 1, [receipt 0 2]⟩) := by decide

theorem paid_suspension_retains_cost_and_mutation :
    let answer := run metered invoice wait 2
      ⟨PUnit.unit, .running false, 0, initial metered 5⟩
    answer.1 = 2 ∧ snapshot answer.2 =
      (.inr (.suspended "worker-7"), 1, ⟨3, none, 1, [receipt 0 2]⟩) := by decide

theorem successful_completion_is_a_distinct_result :
    let answer := run metered invoice finish 2
      ⟨PUnit.unit, .running false, 0, initial metered 5⟩
    answer.1 = 2 ∧ snapshot answer.2 =
      (.inr (.done 42), 1, ⟨3, none, 1, [receipt 0 2]⟩) := by decide

theorem scheduler_pause_can_hold_a_terminal_reply :
    let answer := run metered invoice wait 1
      ⟨PUnit.unit, .running false, 0, initial metered 5⟩
    answer.1 = 2 ∧ snapshot answer.2 =
      (.inl (.terminal (.suspended "worker-7")), 1,
        ⟨3, none, 1, [receipt 0 2]⟩) := by decide

theorem licensed_replay_is_still_paid :
    let answer := run metered invoice tick 2
      ⟨PUnit.unit, .running true, 0, initial metered 5⟩
    answer.1 = 4 ∧ snapshot answer.2 =
      (.inl (.running true), 2, ⟨1, none, 2, [receipt 0 2, receipt 1 2]⟩) := by decide

theorem reusing_a_physical_event_is_refused :
    let answer := run metered (fun _ _ => [receipt 0 2]) tick 3
      ⟨PUnit.unit, .running true, 0, initial metered 5⟩
    answer.1 = 2 ∧ snapshot answer.2 =
      (.inr (.refused .repeatedIdentity), 1, ⟨3, none, 1, [receipt 0 2]⟩) := by decide

theorem unknown_kinds_are_not_free :
    let p : Profile := { metered with kinds := [("step", none)] }
    let answer := run p invoice tick 2 ⟨PUnit.unit, .running false, 0, initial p 5⟩
    answer.1 = 0 ∧ snapshot answer.2 =
      (.inr (.refused .unknownCharge), 0, initial p 5) := by decide

theorem undeclared_kind_is_refused :
    let answer := run metered (fun _ n => [(n, ⟨0, n, .heapLookup, 2⟩)]) tick 2
      ⟨PUnit.unit, .running false, 0, initial metered 5⟩
    answer.1 = 0 ∧ snapshot answer.2 =
      (.inr (.refused .undeclaredKind), 0, initial metered 5) := by decide

def unbounded : Profile := ⟨"zero-work", [], .unknown, none, .refused⟩

def noInvoice (_ : Bool) (_ : Nat) : List Event := []

/-- No finite amount of scheduler fuel can finish this zero-cost handler.
This is why a receipt budget alone proves neither termination nor progress. -/
theorem zero_work_can_continue_forever (fuel world calls budget : Nat) :
    run unbounded noInvoice tick fuel
      ⟨PUnit.unit, .running false, world, ⟨budget, none, calls, []⟩⟩ =
      (0, .paused ⟨PUnit.unit, .running false,
        world + fuel, ⟨budget, none, calls + fuel, []⟩⟩) := by
  induction fuel generalizing world calls with
  | zero => rfl
  | succ fuel ih =>
      change
        (0 + (run unbounded noInvoice tick fuel
          ⟨PUnit.unit, .running false, world + 1, ⟨budget, none, calls + 1, []⟩⟩).1,
          (run unbounded noInvoice tick fuel
            ⟨PUnit.unit, .running false, world + 1, ⟨budget, none, calls + 1, []⟩⟩).2) = _
      rw [ih]
      simp only [Nat.zero_add, Nat.add_assoc, Nat.add_comm 1 fuel]

theorem finite_allowance_stops_zero_work_calls :
    let p : Profile := { unbounded with progress := .bounded, bound := some 2 }
    let answer := run p noInvoice tick 4
      ⟨PUnit.unit, .running false, 0, initial p 0⟩
    answer.1 = 0 ∧ snapshot answer.2 =
      (.inr (.refused .inspectionLimit), 2, ⟨0, some 0, 2, []⟩) := by decide

def countdown (_ : Bool) (world : Nat) : Reply Nat String String × Nat :=
  if world = 0 then (.terminal (.done 0), world) else (.paid, world - 1)

theorem countdown_decreases (replay : Bool) (world : Nat)
    (continues : (countdown replay world).1 = .paid) :
    (countdown replay world).2 < world := by
  by_cases hz : world = 0
  · simp [countdown, hz] at continues
  · simp only [countdown, if_neg hz]
    omega

/-- This actual handler supplies the additional local rank proof that a
progress declaration alone cannot provide. Refusal remains a possible tag. -/
theorem countdown_finite_inspection (world budget : Nat) :
    ∃ (spent : Nat) (result : Finished metered invoice countdown),
      run metered invoice countdown (world + 2)
        ⟨PUnit.unit, .running false, world, initial metered budget⟩ =
          (spent, .done result) := by
  apply ranked_inspection_finishes metered invoice countdown id countdown_decreases
  change world + 1 < world + 2
  omega

theorem countdown_delivers_with_sufficient_budget :
    let answer := run metered invoice countdown 4
      ⟨PUnit.unit, .running false, 2, initial metered 6⟩
    answer.1 = 6 ∧ snapshot answer.2 =
      (.inr (.done 0), 0, ⟨0, none, 3, [receipt 2 2, receipt 1 2, receipt 0 2]⟩) := by decide

#print axioms bounded_complete_slot_account
#print axioms bounded_receipt_discharges_whole_slot
#print axioms yielding_slice_retains_residual
#print axioms unknown_progress_requires_resolution_or_isolation
#print axioms one_dispatch_does_not_bound_work
#print axioms unlimited_is_not_finite_zero
#print axioms ordered_poll_erasure_preserves_occurrences
#print axioms aggregate_forgets_occurrence_order
#print axioms aggregate_forgets_occurrence_partition
#print axioms generic_slot_erasure_forgets_poll_tag
#print axioms aggregate_projection_not_injective
#print axioms no_aggregate_reconstruction
#print axioms admission_poll_projects_exact_aggregate
#print axioms CurrentPublicationControls.invocation_history_covers_paid_account
#print axioms CurrentPublicationControls.issued_generation_is_current
#print axioms CurrentPublicationControls.revoke_then_regrant_does_not_revive_old_generation
#print axioms CurrentPublicationControls.current_cached_decision_returns_reply
#print axioms CurrentPublicationControls.retired_decision_is_unknown_not_execute
#print axioms CurrentPublicationControls.regranted_generation_refuses_cached_decision
#print axioms CurrentPublicationControls.revoked_authority_refuses_cached_decision
#print axioms CurrentPublicationControls.missing_decision_executes
#print axioms CurrentPublicationControls.current_generation_publishes_validated_state
#print axioms CurrentPublicationControls.stale_generation_returns_exact_retry_residual
#print axioms CurrentPublicationControls.current_authority_publishes_validated_state
#print axioms CurrentPublicationControls.authority_refusal_precedes_dependency_conflict
#print axioms CurrentPublicationControls.changed_dependency_returns_exact_retry_residual
#print axioms CurrentPublicationControls.unrelated_change_still_publishes
#print axioms CurrentPublicationControls.committed_publication_is_not_a_delivery_result
#print axioms CurrentPublicationControls.only_committed_publication_enters_delivery
#print axioms CurrentPublicationControls.lost_ack_receipt_recovers_one_durable_effect
#print axioms CurrentPublicationControls.changed_payload_at_same_key_conflicts
#print axioms CurrentPublicationControls.receipt_distinguishes_pending_from_missing
#print axioms CurrentPublicationControls.explicit_unknown_recovery_is_inert
#print axioms CurrentPublicationControls.direct_non_idempotent_replay_can_duplicate
#print axioms HandlerSubstitutionControls.representation
#print axioms HandlerSubstitutionControls.substitution
#print axioms HandlerSubstitutionControls.reverseSubstitution
#print axioms HandlerSubstitutionControls.composed_substitution_recovers_source_state
#print axioms HandlerSubstitutionControls.different_representation_executes_both_phases
#print axioms HandlerSubstitutionControls.current_gate_refusal_retains_pending_root
#print axioms HandlerSubstitutionControls.paid_reply_refusal_retains_selected_phase
#print axioms HandlerSubstitutionControls.both_refusals_can_be_scheduler_pauses
#print axioms HandlerSubstitutionControls.paid_retry_executes_only_selected_suffix
#print axioms HandlerSubstitutionControls.both_refusal_families_transport
#print axioms HandlerSubstitutionControls.submission_reads_account_and_history_survive
#print axioms HandlerSubstitutionControls.current_gate_installation_and_retry_transport
#print axioms HandlerSubstitutionControls.restored_authority_retries_original_phase_once
#print axioms HandlerSubstitutionControls.current_publication_transport
#print axioms HandlerSubstitutionControls.target_publication_checks_current_authority_and_manifest
#print axioms HandlerSubstitutionControls.generation_checked_publication_transport
#print axioms HandlerSubstitutionControls.target_regrant_does_not_revive_stale_handle
#print axioms HandlerSubstitutionControls.changed_gate_has_no_handler_hom
#print axioms HandlerSubstitutionControls.permissive_gate_invents_unauthorized_execution
#print axioms HandlerSubstitutionControls.permissive_gate_has_no_handler_hom
#print axioms HandlerSubstitutionControls.equal_work_does_not_supply_invoice_agreement
#print axioms HandlerSubstitutionControls.changed_invoice_breaks_history_despite_equal_totals
#print axioms HandlerSubstitutionControls.reversed_history_does_not_cover_ordered_account


/-! Concrete body/call realization controls. Source inspections, callback
requests, accepted occurrences and current-policy invoices are observed
separately; none is presented as the cost of a whole native service slot. -/
namespace NativeRetainedControls

open Mettapedia.Machines.SourceProducerCardinality
open Mettapedia.Machines.SourceProducerAdmission
open Cursor.Fold.OwnedSequence.CallbackBoundary

private def build := Nat.add
private def callback (_ left _ : Nat) := left
private def noFallback (_ : List Nat) (_ : Nat) : List Nat := []

abbrev Loan := NativeRetained.Loan build callback noFallback
abbrev Record := NativeRetained.Record Nat Nat Bool
abbrev Call := NativeRetained.Call build callback noFallback (Context := Bool)

def warming (ready : Bool) (_ : Loan) : Bool × Bool := (ready, true)

def actual (quantum : Nat) := NativeRetained.nativeProvider build callback noFallback quantum warming

def initial : Call := NativeRetained.openCall build callback noFallback
  SourceProducerCardinality.Controls.duplicates [] 0 false

def refused : Call := NativeRetained.resume build callback noFallback 64 warming 1 initial

def retried : Call := NativeRetained.resume build callback noFallback 0 warming 1 refused

def continued : Call := NativeRetained.resume build callback noFallback 64 warming 2 retried

structure View where
  callbackCharges : Nat
  pending : Option (List (List Nat))
  terminal : Option BodyCall.Phase
  accepted : Nat
  acceptedRows : List (List Nat)
  consumer : Bool
  replyReady : Bool
  phase : BodyCall.Phase
  sourcePulls : Nat
  requestOrdinal : Nat
  readout : List (List Nat)
  deriving DecidableEq, Repr

def view (call : Call) : View :=
  ⟨call.1, call.2.1.pending.map (fun loan => loan.2.1.rows),
    call.2.1.terminal.map (fun loan => loan.2.2.val.phase), call.2.1.accepted,
    call.2.2.acceptedRows, call.2.2.consumer, call.2.2.cut.val.replyReady,
    call.2.2.cut.val.phase, call.2.2.sourcePulls, call.2.2.requestOrdinal,
    call.2.2.readout build callback⟩

/-- The refused receiver has made a private update but retains its exact
loan. Retrying with no producer quantum accepts that occurrence once. -/
theorem refused_loan_retries_without_source_work :
    view refused = ⟨2, some [[7]], none, 0, [], true, true, .running, 2, 2, [[7], [7]]⟩ ∧
      view retried = ⟨3, none, none, 1, [[7]], true, false, .running, 2, 3, [[7], [7]]⟩ := by
  decide

/-- Equal answer values remain two source occurrences. The last poll earns
exhaustion, separately from the earlier successful acknowledgments. -/
theorem duplicate_occurrences_finish_with_whole_residue :
    view continued =
      ⟨6, none, some .finished, 2, [[7], [7]], true, true, .finished, 5, 6, [[7], [7]]⟩ ∧
      retried.2.1.terminal.isNone = true := by
  decide

/-- Zero acceptance allowance keeps the entire cut, pending loan, callback
state, source account and request ordinal, even with a new source quantum. -/
theorem zero_acceptance_keeps_actual_cut :
    NativeRetained.resume build callback noFallback 99 warming 0 refused = refused :=
  resumeCall_zero _ _ _ _

/-- The acknowledgement request carries a description; only the actual held
reply supplies the accepted payload. It does not confer authority to poll. -/
def forged : Loan :=
  let seed := NativeRetained.openCall build callback noFallback
    [⟨⟨.any, .any⟩, false, .singleton 99⟩] [] 0 true
  let held := (actual 64).step (base := ()) (index := ()) seed.2.2 .next
  held.2.cut.loan build callback noFallback

def forgedAck := (actual 0).step (base := ()) (index := ()) refused.2.2 (.accept forged)

def copiedAck := (actual 64).step (base := ()) (index := ()) forgedAck.2 (.accept forged)

theorem forged_and_copied_acknowledgments_cannot_replace_or_duplicate_the_loan :
    forged.2.1.rows = [[99]] ∧
      forgedAck.1 = true ∧ forgedAck.2.acceptedRows = [[7]] ∧
      copiedAck.1 = false ∧ copiedAck.2.acceptedRows = [[7]] ∧
      copiedAck.2.sourcePulls = refused.2.2.sourcePulls := by
  decide

/-- Exposing a cached reply changes the request account but never invokes
the producer again. A copied reply is not another accepted occurrence. -/
theorem cached_poll_keeps_the_producer_and_loan :
    let cached := (actual 64).step (base := ()) (index := ()) refused.2.2 .next
    cached.2.sourcePulls = refused.2.2.sourcePulls ∧
      cached.2.acceptedRows = [] ∧ cached.2.requestOrdinal = 3 ∧
      (match cached.1 with | .returned loan => loan.2.1.rows | _ => []) = [[7]] := by
  decide

def malformed : NativeRetained.RawCut Nat Nat :=
  { initial.2.2.cut.val with phase := .finished }

theorem mismatched_cut_is_rejected : malformed.check.isNone = true := by decide

def atReading (program : List (Equation Nat)) (reading : NoRuleReading) : Call :=
  (0, ⟨none, none, 0⟩, NativeRetained.Record.ofReference build callback noFallback
    (0, BodyCallOwned.Controls.atReading program reading))

def declined := NativeRetained.resume build callback noFallback 64 warming 1
  (atReading BodyCallRun.missedCons .decline)

def handedOff := NativeRetained.resume build callback noFallback 64 warming 1
  (atReading BodyCallRun.alienAppend (.observe .noAnswers))

def emptyFinished := NativeRetained.resume build callback noFallback 64 warming 1
  (atReading BodyCallRun.missedCons (.observe .noAnswers))

theorem handoff_decline_and_finished_failure_have_distinct_readouts :
    (view declined).terminal = some .declined ∧
      (view handedOff).terminal = some .handoff ∧
      (view emptyFinished).terminal = some .finished ∧
      (view declined).accepted = 0 ∧ (view handedOff).accepted = 0 ∧
      (view emptyFinished).accepted = 0 := by
  decide


open OperationCostProtocol.Indexed

private def permit (_ : Bool) : Except String Unit := .ok ()
private def deny (_ : Bool) : Except String Unit := .error "denied"

def references := NativeRetained.referenceProvider build callback noFallback 64 warming

def sourceGate : Gate (Denied := String) references :=
  NativeRetained.referenceGate build callback noFallback 64 warming permit

def targetGate : Gate (Denied := String) (actual 64) :=
  NativeRetained.nativeGate build callback noFallback 64 warming permit

def deniedGate : Gate (Denied := String) (actual 64) :=
  NativeRetained.nativeGate build callback noFallback 64 warming deny

def profiles : {base : Unit} → {index : Unit} →
    (NativeRetained.CallbackProtocol build callback noFallback).Shape base index → Profile :=
  fun _ => NativeRetained.callbackProfile

def replay : {base : Unit} → {index : Unit} →
    (NativeRetained.CallbackProtocol build callback noFallback).Shape base index → Bool :=
  fun _ => false

def sourceInvoice : Invoice references :=
  NativeRetained.referenceInvoice build callback noFallback 64 warming 17

def targetInvoice : Invoice (actual 64) :=
  NativeRetained.nativeInvoice build callback noFallback 64 warming 17

def substitution := NativeRetained.handler build callback noFallback 64 warming permit 17

def reader := Cursor.Fold.OwnedSequence.CallbackBoundary.client Loan Loan (BodyCallOwned.terminalAfter build callback noFallback)

def continuous : Notice (NativeRetained.CallbackProtocol build callback noFallback) String :=
  fun _ _ => none

def pauseLoan : Notice (NativeRetained.CallbackProtocol build callback noFallback) String :=
  fun request reply => match request with
    | .next => match reply with | .returned _ => some "loan-held" | _ => none
    | .accept _ => none

def seedReference : NativeRetained.ReferenceState build callback noFallback (Context := Bool) :=
  (0, BodyCallOwned.openState build callback noFallback
    SourceProducerCardinality.Controls.duplicates [] 0 true)

def sourcePacket (notice : Notice (NativeRetained.CallbackProtocol build callback noFallback) String) :
    Cursor.Packet (Indexed.provider references sourceGate @profiles @replay sourceInvoice)
      (Indexed.client reader notice) () :=
  ⟨(), .inl (.running 3 none 0), (seedReference, OperationCostProtocol.initial NativeRetained.callbackProfile 100)⟩

def targetPacket (notice : Notice (NativeRetained.CallbackProtocol build callback noFallback) String) :
    Cursor.Packet (Indexed.provider (actual 64) targetGate @profiles @replay targetInvoice)
      (Indexed.client reader notice) () :=
  ⟨(), .inl (.running 3 none 0),
    (NativeRetained.Record.ofReference build callback noFallback seedReference,
      OperationCostProtocol.initial NativeRetained.callbackProfile 100)⟩

def targetRun (notice : Notice (NativeRetained.CallbackProtocol build callback noFallback) String)
    (fuel : Nat) :=
  Indexed.run (actual 64) targetGate @profiles @replay targetInvoice reader notice fuel (targetPacket notice)

/-- The separately executed record provider realizes the actual body/call
source at every cut, including current refusal and reply-dependent notices. -/
theorem indexed_open_run_realizes_actual_source (fuel : Nat)
    (notice : Notice (NativeRetained.CallbackProtocol build callback noFallback) String) :
    let source := Indexed.run references sourceGate @profiles @replay sourceInvoice reader notice
      fuel (sourcePacket notice)
    (source.1, substitution.mapOutcome reader notice source.2) = targetRun notice fuel :=
  substitution.run reader notice fuel (sourcePacket notice)

def privateOf {gate : Gate (Denied := String) (actual 64)}
    {invoice : Invoice (actual 64)}
    {notice : Notice (NativeRetained.CallbackProtocol build callback noFallback) String} :
    Indexed.Outcome (actual 64) gate @profiles @replay invoice reader notice () → Record
  | .paused ⟨_, _, state⟩ => state.1
  | .done ⟨_, _, state⟩ => state.1

private def controlResult : Control Loan Loan → Result Loan Loan
  | .running _ pending accepted => ⟨none, pending, accepted⟩
  | .stopped result => result

def resultOf {gate : Gate (Denied := String) (actual 64)}
    {invoice : Invoice (actual 64)}
    {notice : Notice (NativeRetained.CallbackProtocol build callback noFallback) String} :
    Indexed.Outcome (actual 64) gate @profiles @replay invoice reader notice () → Result Loan Loan
  | .paused ⟨_, .inl control, _⟩ => controlResult control
  | .paused ⟨_, .inr (_, control), _⟩ => controlResult control
  | .done ⟨_, .inl result, _⟩ => result
  | .done ⟨_, .inr (_, control), _⟩ => controlResult control

def refusalOf {gate : Gate (Denied := String) (actual 64)}
    {invoice : Invoice (actual 64)}
    {notice : Notice (NativeRetained.CallbackProtocol build callback noFallback) String} :
    Indexed.Outcome (actual 64) gate @profiles @replay invoice reader notice () → Option (Reason String)
  | .paused ⟨_, .inr (reason, _), _⟩ => some reason
  | .done ⟨_, .inr (reason, _), _⟩ => some reason
  | _ => none

def ledgerView {gate : Gate (Denied := String) (actual 64)}
    {invoice : Invoice (actual 64)}
    {notice : Notice (NativeRetained.CallbackProtocol build callback noFallback) String}
    (result : Nat × Indexed.Outcome (actual 64) gate @profiles @replay invoice reader notice ()) :
    View × Option (Reason String) × Account :=
  (view (result.1, resultOf result.2, privateOf result.2), refusalOf result.2,
    Indexed.accountOf (actual 64) gate @profiles @replay invoice reader notice result.2)

def completed := targetRun continuous 6

def held := targetRun pauseLoan 2

def acknowledged := Indexed.resume (actual 64) targetGate @profiles @replay targetInvoice
  reader pauseLoan 1
  (held.1, Indexed.retry (actual 64) targetGate @profiles @replay targetInvoice reader pauseLoan held.2)

def revoked := Indexed.resume (actual 64) deniedGate @profiles @replay targetInvoice reader pauseLoan 2
  (held.1, Indexed.retry (actual 64) deniedGate @profiles @replay targetInvoice reader pauseLoan
    (Indexed.replaceGate (actual 64) targetGate @profiles @replay targetInvoice reader pauseLoan
      deniedGate held.2))

def reusedInvoice : Invoice (actual 64) := fun _ _ => NativeRetained.requestInvoice 17 0

def repeated := Indexed.resume (actual 64) targetGate @profiles @replay reusedInvoice reader pauseLoan 2
  (held.1, Cursor.Outcome.mapState (Indexed.client reader pauseLoan)
    (source := Indexed.provider (actual 64) targetGate @profiles @replay targetInvoice)
    (target := Indexed.provider (actual 64) targetGate @profiles @replay reusedInvoice)
    (fun state => state)
    (Indexed.retry (actual 64) targetGate @profiles @replay targetInvoice reader pauseLoan held.2))

/-- Split execution transports the actual paid residual, not a new source
call with the same answer value. Notices may stop before or after a reply. -/
theorem indexed_resume_realizes_actual_source (first second : Nat)
    (notice : Notice (NativeRetained.CallbackProtocol build callback noFallback) String) :
    let source := Indexed.run references sourceGate @profiles @replay sourceInvoice reader notice
      first (sourcePacket notice)
    let later := Indexed.resume references sourceGate @profiles @replay sourceInvoice reader notice second source
    (later.1, substitution.mapOutcome reader notice later.2) =
      Indexed.resume (actual 64) targetGate @profiles @replay targetInvoice reader notice second
        (targetRun notice first) := by
  intro source later
  have paired := indexed_open_run_realizes_actual_source first notice
  have resumed := substitution.resume reader notice second source
  rw [show (source.1, substitution.mapOutcome reader notice source.2) = targetRun notice first from paired]
    at resumed
  exact resumed

/-- Both equal occurrences are accepted and the final source marker is
observed. This is five callback requests, with five separate source moves;
those coincident totals are not identified by the interface. -/
theorem checked_execution_keeps_occurrences_and_exact_invoice :
    ledgerView completed =
      (⟨5, none, some .finished, 2, [[7], [7]], true, true, .finished, 5, 5, [[7], [7]]⟩,
        none, ⟨95, none, 5, (List.range 5).flatMap (NativeRetained.requestInvoice 17)⟩) := by
  decide

/-- A post-reply notice retains the loan and charges its real request once.
One subsequent inspection acknowledges that loan without another source pull. -/
theorem checked_post_reply_resume_does_not_reissue_source_work :
    ledgerView held =
      (⟨1, some [[7]], none, 0, [], true, true, .running, 2, 1, [[7], [7]]⟩,
        some (.inl "loan-held"), ⟨99, none, 1, NativeRetained.requestInvoice 17 0⟩) ∧
      ledgerView acknowledged =
      (⟨2, none, none, 1, [[7]], true, false, .running, 2, 2, [[7], [7]]⟩,
        none, ⟨98, none, 2,
          NativeRetained.requestInvoice 17 0 ++ NativeRetained.requestInvoice 17 1⟩) ∧
      (match acknowledged.2 with | .paused _ => true | .done _ => false) = true := by
  decide

/-- A current revocation refuses the next reliance while preserving the
previously paid source reply and its full unacknowledged occurrence. -/
theorem revocation_cannot_accept_or_erase_a_retained_reply :
    ledgerView revoked =
      ((ledgerView held).1, some (.inl "denied"), (ledgerView held).2.2) := by
  decide

/-- Restarting the request ordinal would reuse an invoice identity. The
existing account rejects that attempt before acceptance or further source work. -/
theorem repeated_invoice_cannot_replay_the_held_acknowledgment :
    ledgerView repeated =
      ((ledgerView held).1, some (.inr .repeatedIdentity), (ledgerView held).2.2) := by
  decide

/-- A scheduler pause is not exhaustion and does not erase the remaining
source alternatives merely because no answer has yet been exposed. -/
theorem zero_inspections_preserve_nonempty_source_residual :
    let zero := (ledgerView (targetRun continuous 0)).1
    zero.callbackCharges = 0 ∧ zero.accepted = 0 ∧ zero.terminal = none ∧
      zero.sourcePulls = 0 ∧ zero.requestOrdinal = 0 ∧ zero.replyReady = false ∧
      zero.readout = [[7], [7]] := by
  decide

/-- Equal aggregate work cannot replace the ordered interaction history. -/
theorem reversed_actual_invoice_is_not_the_same_history :
    let events := (ledgerView completed).2.2.events
    OperationCostProtocol.work events.reverse = OperationCostProtocol.work events ∧
      ¬ events.Sublist events.reverse := by
  decide

#print axioms refused_loan_retries_without_source_work
#print axioms duplicate_occurrences_finish_with_whole_residue
#print axioms zero_acceptance_keeps_actual_cut
#print axioms forged_and_copied_acknowledgments_cannot_replace_or_duplicate_the_loan
#print axioms cached_poll_keeps_the_producer_and_loan
#print axioms mismatched_cut_is_rejected
#print axioms handoff_decline_and_finished_failure_have_distinct_readouts
#print axioms indexed_open_run_realizes_actual_source
#print axioms indexed_resume_realizes_actual_source
#print axioms checked_execution_keeps_occurrences_and_exact_invoice
#print axioms checked_post_reply_resume_does_not_reissue_source_work
#print axioms revocation_cannot_accept_or_erase_a_retained_reply
#print axioms repeated_invoice_cannot_replay_the_held_acknowledgment
#print axioms zero_inspections_preserve_nonempty_source_residual
#print axioms reversed_actual_invoice_is_not_the_same_history

end NativeRetainedControls

namespace DutySettlementControls

open Mettapedia.Machines.ErrorBoundaryContracts.DispatchPermit
open Mettapedia.Machines.ErrorBoundaryContracts
open DurableEscrow DurableEscrow.RetainedSettlement
open OperationCostProtocol.Indexed
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone (Handle)

def keys : Keys := ⟨10, 20, 30⟩
def primary : Request := ⟨3, 0, .primary⟩
def repair : Request := ⟨3, 0, .repair⟩
def origin : Nat := 73
def account : Account := initial readProfile 10

def snapshot (service : Service) (grants : List (AttemptIdentity.DurableDuty.Grant Nat Nat)) : Store :=
  fun key => if key = keys.localState then .localState service
    else if key = keys.policy then .policy grants
    else if key = keys.receiver then .receiver service.remote else .absent

def before : Service := DurableEscrow.Controls.persisted true
def authority := DurableEscrow.Controls.grants
def captured : Store := snapshot before authority
def allow (store : Store) : RetainedSettlement.Gate store := fun _ _ => .ok ()
def deny (store : Store) : RetainedSettlement.Gate store := fun _ _ => .error .policy
def continuous : RetainedSettlement.Notice := fun _ _ => none
def afterPolicy : RetainedSettlement.Notice := fun key _ => if key = keys.policy then some .policy else none

def plan : Plan := ⟨before, authority, before.remote, before.adopt authority 3 0 .primary⟩
def reads : ReadOnlyQuery.Reads Nat Cell :=
  [(30, .receiver before.remote), (20, .policy authority), (10, .localState before)]
def events : List Event :=
  [(0, ⟨73, 0, .quantum, 1⟩), (1, ⟨73, 1, .quantum, 1⟩), (2, ⟨73, 2, .quantum, 1⟩)]
def paid : Account := ⟨7, none, 3, events⟩
def held := RetainedSettlement.start captured keys primary (allow captured) origin continuous account 4

theorem finished : held.outcome = .done ⟨.unit, .inl (.ok plan), (reads, paid)⟩ := rfl

theorem executed : Executed captured keys primary origin continuous account held :=
  Executed.start (allow captured) 4

theorem actual_settlement_uses_all_reads_and_exact_logical_invoice :
    held.spent = 3 ∧ held.account = paid ∧
      plan.after = DurableEscrow.Controls.adopted ∧
      plan.after.remote.balance = 7 ∧ plan.after.remote.history = [.debit 0 3] ∧
      (plan.after.ledger.rows[0]?).map (fun row => row.primary.task.acknowledged) = some true := by
  decide

def paused := RetainedSettlement.start captured keys primary (allow captured) origin afterPolicy account 3
def denied := paused.resumeWith (source captured) (allow captured) (fun _ => readProfile)
  (fun _ => false) (RetainedSettlement.invoice captured origin) reader afterPolicy (deny captured) 2
def resumed := denied.resumeWith (source captured) (deny captured) (fun _ => readProfile)
  (fun _ => false) (RetainedSettlement.invoice captured origin) reader afterPolicy (allow captured) 2

theorem paid_refusal_and_current_revocation_keep_the_exact_receiver_request :
    paused.spent = 2 ∧ paused.account.remaining = 8 ∧
      denied.spent = 2 ∧ denied.account = paused.account ∧
      denied.submission = paused.submission ∧
      RetainedSettlement.observation captured denied.outcome =
        ReadOnlyQuery.run captured (query keys primary) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact (resumeWith_observation ..).trans (start_observation ..)

theorem rearming_runs_only_the_unread_receiver_suffix :
    resumed.spent = 3 ∧ resumed.account = paid ∧
      resumed.outcome = .done ⟨.unit, .inl (.ok plan), (reads, paid)⟩ := by
  exact ⟨rfl, rfl, rfl⟩

def firstRefused := RetainedSettlement.start captured keys primary (deny captured) origin continuous account 2

theorem refusal_is_not_absence_or_a_free_settlement :
    firstRefused.spent = 0 ∧ firstRefused.account = account ∧
      firstRefused.outcome = .done
        ⟨.unit, .inr (.inl .policy, query keys primary), ([], account)⟩ := by
  exact ⟨rfl, rfl, rfl⟩

def history : NativePoll.History := [⟨false, .complete, events.map fun event => (.sourceWork, event)⟩]

theorem actual_paid_account_has_ordered_model_history :
    Indexed.Invocation.PollHistoryCovers (source := source captured) (gate := allow captured)
      (profiles := fun _ => readProfile) (replay := fun _ => false)
      (invoice := RetainedSettlement.invoice captured origin) (reader := reader)
      (notice := continuous) held history := by
  unfold Indexed.Invocation.PollHistoryCovers
  rw [actual_settlement_uses_all_reads_and_exact_logical_invoice.2.1]
  simp [paid, history, NativePoll.historyEvents, NativePoll.receiptEvents]

def handle : Handle Nat Nat := ⟨99, 7, 1⟩
def regrantedHandle : Handle Nat Nat := ⟨99, 7, 3⟩
def requirement : CheckedGrant.Requirement Nat Nat Access := ⟨handle, .consume⟩

local instance : Decidable (FrameUpdate CurrentPublicationControls.currentPoint.authority requirement.required) :=
  CurrentPublicationControls.accessPermission .consume .consume

def publishAt (point : IndexedAuthority.Point revocationWorlds) (currentHandle : Handle Nat Nat)
    (current : Store) :=
  letI : Decidable (FrameUpdate point.authority requirement.required) :=
    CurrentPublicationControls.accessPermission point.authority .consume
  RetainedSettlement.publish executed plan (reads, paid) finished history
    revocationWorlds point requirement currentHandle .policy current

theorem current_generation_publishes_the_actual_semantic_adoption :
    publishAt CurrentPublicationControls.currentPoint handle captured =
      .committed (ValidatedCommit.write captured [(10, .localState plan.after)]) history := rfl

theorem equal_right_regrant_does_not_revive_the_old_duty_invocation :
    publishAt CurrentPublicationControls.currentPoint regrantedHandle captured =
      .authorityRefused .policy held history := rfl

theorem current_host_revocation_keeps_the_already_paid_result :
    publishAt CurrentPublicationControls.revokedPoint handle captured =
      .authorityRefused .policy held history := rfl

theorem changed_application_policy_refuses_publication_and_keeps_the_whole_invocation :
    publishAt CurrentPublicationControls.currentPoint handle
        (Function.update captured 20 (.policy [])) =
      .dependencyConflict held history := rfl

theorem cancellation_after_capture_requires_a_new_semantic_decision :
    publishAt CurrentPublicationControls.currentPoint handle
        (Function.update captured 10 (.localState (serviceStep before (.cancel 0)))) =
      .dependencyConflict held history := rfl

theorem changed_receiver_evidence_cannot_reuse_a_completed_primary_reply :
    publishAt CurrentPublicationControls.currentPoint handle
        (Function.update captured 30 (.receiver DurableEscrow.Controls.compensated.remote)) =
      .dependencyConflict held history := rfl

theorem current_application_revocation_cannot_mint_a_disposition :
    (ReadOnlyQuery.run (snapshot before []) (query keys primary)).answer = .error .notAdopted ∧
      (before.adopt [] 3 0 .primary) = before := by decide

theorem missing_receiver_evidence_is_an_explicit_negative_read :
    let missing := Function.update captured 30 Cell.absent
    (ReadOnlyQuery.run missing (query keys primary)).answer = .error .receiver ∧
      (ReadOnlyQuery.run missing (query keys primary)).reads =
        [(10, .localState before), (20, .policy authority), (30, .absent)] := by
  exact ⟨rfl, rfl⟩

theorem remote_acceptance_and_crash_uncertainty_are_not_a_settleable_answer :
    (ReadOnlyQuery.run (snapshot (DurableEscrow.Controls.accepted true).crash authority)
      (query keys primary)).answer = .error .notAdopted ∧
      (DurableEscrow.Controls.accepted true).crash.remote.balance = 7 := by decide

def repairBefore : Service := DurableEscrow.Controls.repairPersisted
def repairSnapshot : Store := snapshot repairBefore authority
def repairPlan : Plan :=
  ⟨repairBefore, authority, repairBefore.remote, repairBefore.adopt authority 3 0 .repair⟩
def repaired := RetainedSettlement.start repairSnapshot keys repair (allow repairSnapshot)
  origin continuous account 4

theorem compensation_settles_after_real_cancel_restart_and_refund :
    RetainedSettlement.observation repairSnapshot repaired.outcome =
      ⟨.ok repairPlan, [(10, .localState repairBefore), (20, .policy authority),
        (30, .receiver repairBefore.remote)]⟩ ∧
      repairPlan.after = DurableEscrow.Controls.compensated ∧
      repairPlan.after.remote.balance = 10 ∧
      repairPlan.after.remote.history = [.debit 0 3, .refund 0 3] := by
  exact ⟨rfl, by decide, by decide, by decide⟩

theorem irreversible_effect_cannot_become_a_successful_repair_readout :
    (ReadOnlyQuery.run (snapshot DurableEscrow.Controls.uncompensated authority)
      (query keys repair)).answer = .error .notAdopted ∧
      DurableEscrow.Controls.uncompensated.remote.balance = 7 ∧
      DurableEscrow.Controls.uncompensated.remote.history = [.debit 0 3] := by decide

/-- The second handler appends observations chronologically. It is an
independently defined provider, not the source provider under another name. -/
def chronologicalProvider (store : Store) :
    Cursor.Provider (Cursor.ReadOnlyQuery.protocol Nat Cell) where
  State _ _ := ReadOnlyQuery.Reads Nat Cell
  step prior key := ⟨store key, prior ++ [(key, store key)]⟩

set_option backward.isDefEq.respectTransparency false in
def chronologicalRepresentation (store : Store) :
    Cursor.Hom (source store) (chronologicalProvider store) where
  map reads := reads.reverse
  step reads key := by
    change (⟨store key, ((key, store key) :: reads).reverse⟩ :
      Σ _ : Cell, ReadOnlyQuery.Reads Nat Cell) = ⟨store key, reads.reverse ++ [(key, store key)]⟩
    rw [List.reverse_cons]

def chronologicalGate (store : Store) : Indexed.Gate (Denied := RetainedSettlement.Refused)
    (chronologicalProvider store) := fun _ _ => .ok ()

def chronologicalInvoice (store : Store) : Indexed.Invoice (chronologicalProvider store) :=
  fun history _ => [(history.length, ⟨73, history.length, .quantum, 1⟩)]

set_option backward.isDefEq.respectTransparency false in
def handler : Indexed.HandlerHom (source captured) (chronologicalProvider captured)
    (allow captured) (chronologicalGate captured) (fun _ => readProfile) (fun _ => readProfile)
    (fun _ => false) (fun _ => false) (RetainedSettlement.invoice captured origin)
    (chronologicalInvoice captured) where
  representation := chronologicalRepresentation captured
  gate_eq _ _ := rfl
  profiles_eq _ := rfl
  replay_eq _ := rfl
  invoice_eq reads _ := by
    change ([(reads.length, ⟨73, reads.length, .quantum, 1⟩)] : List Event) =
      [(reads.reverse.length, ⟨73, reads.reverse.length, .quantum, 1⟩)]
    rw [List.length_reverse]

def chronologicalRun := Indexed.run (chronologicalProvider captured) (chronologicalGate captured)
  (fun _ => readProfile) (fun _ => false) (chronologicalInvoice captured) reader continuous (base := .unit) 4
  ⟨.unit, .inl (query keys primary), [], account⟩

theorem different_handler_really_executes_the_semantic_duty_query :
    chronologicalRun = (3, .done ⟨.unit, .inl (.ok plan), (reads.reverse, paid)⟩) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem local_handler_laws_reach_that_actual_execution :
    (handler.invocation reader continuous held).outcome = chronologicalRun.2 := by
  simpa only [held, RetainedSettlement.start, chronologicalRun, Indexed.HandlerHom.invocation,
    Cursor.Hom.packet, Indexed.HandlerHom.lift, handler, chronologicalRepresentation,
    List.reverse_nil] using congrArg Prod.snd (handler.run reader continuous (base := .unit) 4
      ⟨.unit, .inl (query keys primary), [], account⟩)

set_option backward.isDefEq.respectTransparency false in
theorem handler_substitution_preserves_paid_account_and_current_publication :
    (handler.invocation reader continuous held).account = paid ∧
      RetainedSettlement.publishVia handler executed plan (reads, paid) finished history
        revocationWorlds CurrentPublicationControls.currentPoint requirement handle .policy captured =
        .committed (ValidatedCommit.write captured [(10, .localState plan.after)]) history := by
  constructor
  · rw [handler.invocation_account]
    exact actual_settlement_uses_all_reads_and_exact_logical_invoice.2.1
  · rw [← RetainedSettlement.publishVia_commutes]
    change handler.publication reader continuous
      (publishAt CurrentPublicationControls.currentPoint handle captured) = _
    rw [current_generation_publishes_the_actual_semantic_adoption]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem substituted_handler_cannot_restore_a_revoked_generation :
    RetainedSettlement.publishVia handler executed plan (reads, paid) finished history
        revocationWorlds CurrentPublicationControls.currentPoint requirement regrantedHandle .policy captured =
      .authorityRefused .policy (handler.invocation reader continuous held) history := by
  rw [← RetainedSettlement.publishVia_commutes]
  change handler.publication reader continuous
    (publishAt CurrentPublicationControls.currentPoint regrantedHandle captured) = _
  rw [equal_right_regrant_does_not_revive_the_old_duty_invocation]
  rfl

def wrongInvoice : Indexed.Invoice (chronologicalProvider captured) :=
  fun _ _ => [(0, ⟨73, 0, .quantum, 2⟩)]

theorem mismatched_invoice_has_no_handler_substitution :
    ¬ Nonempty (Indexed.HandlerHom (source captured) (chronologicalProvider captured)
      (allow captured) (chronologicalGate captured) (fun _ => readProfile) (fun _ => readProfile)
      (fun _ => false) (fun _ => false) (RetainedSettlement.invoice captured origin) wrongInvoice) := by
  rintro ⟨claimed⟩
  have impossible := claimed.invoice_eq (base := .unit) (index := .unit) [] 10
  simp [RetainedSettlement.invoice, wrongInvoice, origin] at impossible

def chronologicalDenied : Indexed.Gate (Denied := RetainedSettlement.Refused)
    (chronologicalProvider captured) := fun _ _ => .error .policy

theorem mismatched_gate_has_no_handler_substitution :
    ¬ Nonempty (Indexed.HandlerHom (source captured) (chronologicalProvider captured)
      (allow captured) chronologicalDenied (fun _ => readProfile) (fun _ => readProfile)
      (fun _ => false) (fun _ => false) (RetainedSettlement.invoice captured origin)
      (chronologicalInvoice captured)) := by
  rintro ⟨claimed⟩
  have impossible := claimed.gate_eq (base := .unit) (index := .unit) [] 10
  simp [allow, chronologicalDenied] at impossible

end DutySettlementControls

end Mettapedia.GSLT.LanguageDef.OperationCostProtocolControls
