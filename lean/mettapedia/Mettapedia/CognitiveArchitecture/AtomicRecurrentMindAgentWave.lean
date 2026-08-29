import Mettapedia.CognitiveArchitecture.RecurrentParallelMindAgentWave
import Mettapedia.CognitiveArchitecture.RecurrentMindAgentBackpressure
import Mettapedia.GSLT.Core.AtomicDeferredDisposition

/-!
# Atomic recurrent mind-agent cycles

The checked recurrent portfolio generates one exact five-occurrence cycle:
ECAN, incremental compression, PLN, premise selection, and foreground
chaining.  Its monotone receipt semantics and paired STI/LTI accounts already
earn a certified parallel wave.

This module carries that real recurrent batch through the generic atomic
snapshot boundary.  A successful decision publishes the complete occurrence
bag at one fresh revision and consumes the exact paired account.  A revision
conflict publishes none of it, spends nothing, and retains the complete cycle
as pending.  Checked recurrence, generation, selection, and funding still
cannot accept a last-writer-wins batch that lacks observer serializability.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.AtomicRecurrentMindAgentWave

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.CognitiveArchitecture.AttentionEconomyResourceControl
open Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio
open Mettapedia.CognitiveArchitecture.RecurrentMindAgentBackpressure
open Mettapedia.CognitiveArchitecture.RecurrentParallelMindAgentWave
open Mettapedia.CognitiveArchitecture.RecurrentParallelMindAgentWave.Canary
open Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
open Mettapedia.GSLT.Core.AtomicCertifiedBatchCommit
open Mettapedia.GSLT.Core.AtomicCertifiedBatchFamily
open Mettapedia.GSLT.Core.AtomicDeferredDisposition.DeferredContext
open Mettapedia.GSLT.Core.AtomicSnapshotTransaction
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl

noncomputable section

abbrev Proposal := CapturedBatchProposal Nat cycleCertified

def proposal : Proposal :=
  { capturedRevision := 20
    bulkAuthorized := recurrentCycleWave.completeBag_dispatches_bulk rfl }

abbrev spec : Spec Nat (Multiset Item) Item Proposal :=
  transactionSpec (Revision := Nat) (certified := cycleCertified)

def live : Snapshot Nat (Multiset Item) := ⟨20, 0⟩

def receipt : CommitReceipt spec proposal live where
  current := ⟨rfl, rfl⟩
  nextRevision := 21
  advanced := by decide

def committed : Decision spec proposal live := .committed receipt

/-- The actual five-role checked cycle remains recurrent and generated while
crossing the physical boundary as one complete atomic revision. -/
theorem checked_recurrent_cycle_commits_atomically :
    portfolioClaim.Meaning foregroundAccepting ∧
      (cycleBatch.map fun item => item.resident) =
        [.ecan, .incrementalCompression, .pln, .premiseSelection,
          .foregroundChaining] ∧
      (forall item, item ∈ cycleBatch ->
        serviceSpace.Generated heartbeatTrace item.generatedAt item) ∧
      (forall item, item ∈ cycleBatch ->
        exists offset, offset < 1 ∧
          selectedGenerated (item.generatedAt + offset) item) ∧
      (recurrentCycleWave.admission.certified.plan .general).activation =
        .bulk ∧
      committed.physicalSnapshot =
        ⟨21, (cycleBatch : Multiset Item)⟩ ∧
      CapturedBatchProposal.accountAfter committed = 0 ∧
      committed.ledger.executed = (cycleBatch : Multiset Item) ∧
      committed.ledger.pending = 0 := by
  rcases checked_cycle_earns_parallel_wave with
    ⟨recurrence, residentOrder, generated, selected, _shortFunding,
      _longFunding, bulk⟩
  exact ⟨recurrence, residentOrder, generated, selected, bulk,
    rfl, rfl, rfl, rfl⟩

/-- The two independently typed attention instruments retain their exact
additive decomposition at the atomic publication boundary. -/
theorem recurrent_attention_is_conserved_at_commit :
    (shortSourceFor cycleBatch, longSourceFor cycleBatch) =
      batchDemand (fun item => (shortDemand item, longDemand item))
          cycleBatch +
        CapturedBatchProposal.accountAfter committed :=
  CapturedBatchProposal.committed_account_conservation receipt

def staleLive : Snapshot Nat (Multiset Item) := ⟨21, 0⟩

def staleConflict : ¬ Matches spec proposal staleLive := by
  intro current
  have revisionImpossible := current.revision_eq
  norm_num [staleLive, spec,
    Mettapedia.GSLT.Core.AtomicCertifiedBatchCommit.transactionSpec,
    proposal] at revisionImpossible

def staleDecision : Decision spec proposal staleLive :=
  .deferred staleConflict

/-- A stale recurrent wave is an all-or-nothing rollback of its occurrence
store, both attention accounts, and all five exact generated occurrences. -/
theorem stale_cycle_rolls_back_state_attention_and_work :
    staleDecision.physicalSnapshot = staleLive ∧
      CapturedBatchProposal.accountAfter staleDecision =
        (shortSourceFor cycleBatch, longSourceFor cycleBatch) ∧
      staleDecision.ledger.executed = 0 ∧
      staleDecision.ledger.pending = (cycleBatch : Multiset Item) :=
  CapturedBatchProposal.deferred_rolls_back_state_account_and_batch
    staleConflict

/-- Deferral retains the authored occurrence order needed by FIFO/age
controllers.  Its erasure is exactly the bag ledger, and the existing finite
capacity schedule drains that same ordered cycle without loss. -/
theorem stale_cycle_retains_order_for_exact_reoffer :
    staleDecision.orderedLedger.pending = cycleBatch ∧
      (staleDecision.orderedLedger.pending : Multiset Item) =
        staleDecision.ledger.pending ∧
      threeRounds.serviced.map (fun item => item.resident) =
        [.ecan, .incrementalCompression, .pln, .premiseSelection,
          .foregroundChaining] ∧
      threeRounds.pending = [] := by
  refine ⟨rfl, ?_, three_rounds_drain_complete_cycle⟩
  exact (staleDecision.orderedLedger_erases_to_ledger).2

/-! ## Fresh certification after an intervening commit -/

/-- Monotone receipt accumulation is certifiable at every source state, not
only at the empty worked fixture. -/
def cycleCertifiedAt (initial : Multiset Item) :
    CertifiedBatch contract monotoneSemantics initial
      (initial + (cycleBatch : Multiset Item))
      (ImportanceAccount Role Nat)
      (fun item => (shortDemand item, longDemand item))
      (shortSourceFor cycleBatch, longSourceFor cycleBatch) cycleBatch where
  nonempty := by decide
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · rfl
    · intro ordering permutation
      refine ⟨initial + (ordering : Multiset Item), rfl, ?_⟩
      exact congrArg (fun suffix : Multiset Item => initial + suffix)
        (Quot.sound permutation)
  resources := pairFunding (shortSeparation cycleBatch)
    (longSeparation cycleBatch)

def cycleFamily :
    BulkCertifiedBatchFamily contract monotoneSemantics
      (ImportanceAccount Role Nat)
      (fun item => (shortDemand item, longDemand item))
      (shortSourceFor cycleBatch, longSourceFor cycleBatch) cycleBatch where
  targetAt initial := initial + (cycleBatch : Multiset Item)
  certifiedAt := cycleCertifiedAt
  bulkAuthorizedAt initial :=
    (cycleCertifiedAt initial).completeBag_dispatches_bulk rfl

/-- One already-published receipt distinguishes the intervening physical
state from the empty source of the stale proposal. -/
def ambientReceipt : Item :=
  { generatedAt := 99
    trigger := ()
    resident := .pln }

def changedLive : Snapshot Nat (Multiset Item) :=
  ⟨21, {ambientReceipt}⟩

def changedOldConflict : ¬ Matches spec proposal changedLive := by
  intro current
  have revisionImpossible := current.revision_eq
  norm_num [changedLive, spec,
    Mettapedia.GSLT.Core.AtomicCertifiedBatchCommit.transactionSpec,
    proposal] at revisionImpossible

abbrev FamilyProposal := CapturedFamilyProposal Nat cycleFamily

def freshProposal : FamilyProposal := captureLive changedLive

abbrev familySpec : Spec Nat (Multiset Item) Item FamilyProposal :=
  Mettapedia.GSLT.Core.AtomicCertifiedBatchFamily.transactionSpec
    (Revision := Nat) (family := cycleFamily)

def freshReceipt : CommitReceipt familySpec freshProposal changedLive where
  current := captureLive_matches changedLive
  nextRevision := 22
  advanced := by decide

def freshCommitted : Decision familySpec freshProposal changedLive :=
  .committed freshReceipt

/-- Safe retry means constructing a fresh source-indexed certificate.  The old
proposal remains stale; the fresh one preserves the intervening receipt and
adds the complete checked cycle atomically. -/
theorem retry_requires_fresh_state_indexed_certificate :
    ¬ Matches spec proposal changedLive ∧
      Matches familySpec freshProposal changedLive ∧
      freshCommitted.physicalSnapshot =
        ⟨22, ({ambientReceipt} : Multiset Item) +
          (cycleBatch : Multiset Item)⟩ ∧
      Mettapedia.GSLT.Core.AtomicCertifiedBatchFamily.CapturedFamilyProposal.accountAfter
          freshCommitted = 0 ∧
      freshCommitted.ledger.executed = (cycleBatch : Multiset Item) := by
  exact ⟨changedOldConflict, captureLive_matches changedLive,
    rfl, rfl, rfl⟩

/-! ## The complete post-conflict policy envelope -/

/-- The family-level version of the original cycle proposal. -/
def oldFamilyProposal : FamilyProposal :=
  ⟨⟨20, 0⟩⟩

def familyConflict : ¬ Matches familySpec oldFamilyProposal changedLive := by
  intro current
  have revisionImpossible := current.revision_eq
  norm_num [changedLive, familySpec,
    Mettapedia.GSLT.Core.AtomicCertifiedBatchFamily.transactionSpec,
    oldFamilyProposal] at revisionImpossible

def deferredContext :
    Mettapedia.GSLT.Core.AtomicDeferredDisposition.DeferredContext
      Nat cycleFamily where
  proposal := oldFamilyProposal
  live := changedLive
  conflict := familyConflict

/-- Occurrence receipts form a commutative, non-idempotent delta algebra.
Non-idempotence is essential: repeated task occurrences remain repeated work. -/
def occurrenceDeltaAlgebra :
    Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.DeltaAlgebra
      (Multiset Item) (Multiset Item) where
  empty := 0
  compose := (· + ·)
  apply := (· + ·)
  compose_assoc := add_assoc
  empty_compose := zero_add
  compose_empty := add_zero
  apply_empty := add_zero
  apply_compose := fun state first second =>
    (add_assoc state first second).symm

/-- Merge every isolated occurrence delta by multiset addition.  Unlike a set
join, this resolver preserves multiplicity. -/
def occurrenceMerge :
    Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.AlternativeMerge
      (Multiset Item) where
  merge deltas := some deltas.sum
  permutationInvariant := by
    intro first second permutation
    apply congrArg some
    have bags : (first : Multiset (Multiset Item)) =
        (second : Multiset (Multiset Item)) :=
      Quot.sound permutation
    simpa using congrArg
      (fun items : Multiset (Multiset Item) => items.sum) bags

abbrev ReceiptProgram :=
  Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.Program
    (Multiset Item) (Multiset Item) Item Unit

def occurrenceBranch (item : Item) : ReceiptProgram :=
  .update {item} (.pure item)

/-- Turn one known nonempty occurrence list into an isolated branch family
without adding a sentinel branch. -/
def chooseAll : Item → List Item → ReceiptProgram
  | item, [] => occurrenceBranch item
  | item, next :: rest =>
      .choose (occurrenceBranch item) (chooseAll next rest)

def cycleFirst : Item :=
  cycleBatch.get ⟨0, by decide⟩

def cycleProgram : ReceiptProgram :=
  chooseAll cycleFirst (cycleBatch.drop 1)

def worldWork
    (world : Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.DeltaWorld
      (Multiset Item) (Multiset Item) Item PUnit) : Item :=
  world.answer

/-- Serial fallback is reinterpreted from the current occurrence store.  The
reverse order remains observer-equivalent because the observer is a multiset,
while the receipt retains that reverse order explicitly. -/
def reverseSerialReceipt : FreshSerialReceipt deferredContext where
  ordering := cycleBatch.reverse
  sameOccurrences := cycleBatch.reverse_perm
  target := changedLive.state + (cycleBatch.reverse : Multiset Item)
  run := rfl
  observesFreshTarget := by
    exact congrArg (fun suffix : Multiset Item => changedLive.state + suffix)
      (Quot.sound cycleBatch.reverse_perm)
  nextRevision := 22
  advanced := by decide

/-- The same fresh state may instead be reached by isolated occurrence
branches followed by the authored multiplicity-preserving merge.  All branch
worlds remain in the receipt. -/
def occurrenceMergeReceipt :
    FreshMergeReceipt deferredContext occurrenceDeltaAlgebra occurrenceMerge
      cycleProgram worldWork where
  merged :=
    show Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.Merged
        (Multiset Item) (Multiset Item) Item Unit from
      { worlds :=
        Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.runWorlds
          occurrenceDeltaAlgebra cycleProgram changedLive.state
        delta := (cycleBatch : Multiset Item)
        state := changedLive.state + (cycleBatch : Multiset Item) }
  resolved := by decide
  coversPending := by decide
  observesFreshTarget := rfl
  nextRevision := 22
  advanced := by decide

abbrev CycleDisposition :=
  Disposition deferredContext occurrenceDeltaAlgebra occurrenceMerge
    cycleProgram worldWork

def suspendedCycle : CycleDisposition := .suspend
def refreshedCycle : CycleDisposition := .refresh deferredContext.freshRetry
def serializedCycle : CycleDisposition := .serialize reverseSerialReceipt
def mergedCycle : CycleDisposition := .merge occurrenceMergeReceipt

/-- The real five-role batch inhabits every branch of the policy-neutral
envelope.  Suspension and refresh leave it pending; serial and merge advance
the complete current state while preserving every occurrence and the paired
attention account. -/
theorem recurrent_cycle_dispositions_preserve_state_work_and_attention :
    suspendedCycle.pendingWork = cycleBatch ∧
      refreshedCycle.physicalSnapshot = changedLive ∧
      serializedCycle.physicalSnapshot =
        ⟨22, changedLive.state + (cycleBatch : Multiset Item)⟩ ∧
      mergedCycle.physicalSnapshot =
        ⟨22, changedLive.state + (cycleBatch : Multiset Item)⟩ ∧
      (serializedCycle.executedWork : Multiset Item) =
        (cycleBatch : Multiset Item) ∧
      occurrenceMergeReceipt.merged.worlds.map worldWork = cycleBatch ∧
      (shortSourceFor cycleBatch, longSourceFor cycleBatch) =
        mergedCycle.chargedDemand + mergedCycle.accountAfter := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, mergedCycle.account_conservation⟩
  · change
      (⟨22, changedLive.state + (cycleBatch.reverse : Multiset Item)⟩ :
        Snapshot Nat (Multiset Item)) =
        ⟨22, changedLive.state + (cycleBatch : Multiset Item)⟩
    exact congrArg
      (fun suffix : Multiset Item =>
        (⟨22, changedLive.state + suffix⟩ : Snapshot Nat (Multiset Item)))
      (Quot.sound cycleBatch.reverse_perm)
  · rfl
  · exact reverseSerialReceipt.occurrenceBag_exact
  · exact occurrenceMergeReceipt.occurrenceOrder_exact

/-- Multiplicity is not optional for recurrent work: adding the same
occurrence delta twice is observably different from adding it once. -/
theorem occurrence_merge_is_not_idempotent :
    let item := cycleFirst
    occurrenceMerge.merge [{item}, {item}] = some ({item, item} : Multiset Item) ∧
      occurrenceMerge.merge [{item}] = some ({item} : Multiset Item) ∧
      ({item, item} : Multiset Item) ≠ {item} := by
  decide

abbrev ConflictingCertified :=
  CertifiedBatch contract overwriteSemantics .foregroundChaining
    .incrementalCompression (ImportanceAccount Role Nat)
    (fun item => (shortDemand item, longDemand item))
    (shortSourceFor conflictingBatch, longSourceFor conflictingBatch)
    conflictingBatch

/-- Recurrence and exact paired funding cannot manufacture an atomic proposal
for generated work whose two execution orders have different observations. -/
theorem conflicting_recurrent_work_cannot_enter_atomic_boundary :
    Nonempty
        (BatchSeparation (Fund .shortTerm Role Nat)
          shortDemand (shortSourceFor conflictingBatch) conflictingBatch) ∧
      Nonempty
        (BatchSeparation (Fund .longTerm Role Nat)
          longDemand (longSourceFor conflictingBatch) conflictingBatch) ∧
      ¬ Nonempty
        (Σ certifiedConflict : ConflictingCertified,
          CapturedBatchProposal Nat certifiedConflict) := by
  refine ⟨⟨shortSeparation conflictingBatch⟩,
    ⟨longSeparation conflictingBatch⟩, ?_⟩
  rintro ⟨certifiedConflict, _proposal⟩
  exact overwrite_not_serializable
    certifiedConflict.executionSerializable

#print axioms checked_recurrent_cycle_commits_atomically
#print axioms recurrent_attention_is_conserved_at_commit
#print axioms stale_cycle_rolls_back_state_attention_and_work
#print axioms stale_cycle_retains_order_for_exact_reoffer
#print axioms retry_requires_fresh_state_indexed_certificate
#print axioms recurrent_cycle_dispositions_preserve_state_work_and_attention
#print axioms occurrence_merge_is_not_idempotent
#print axioms conflicting_recurrent_work_cannot_enter_atomic_boundary

end

end Mettapedia.CognitiveArchitecture.AtomicRecurrentMindAgentWave
