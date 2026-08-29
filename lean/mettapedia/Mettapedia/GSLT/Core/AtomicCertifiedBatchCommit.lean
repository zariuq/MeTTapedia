import Mettapedia.GSLT.Core.AtomicSnapshotTransaction

/-!
# Atomic realization of generic certified batches

`CertifiedBatch` relates an occurrence batch to an observer, an execution
semantics, and an additive resource account.  It does not by itself publish
the reference target into ambient state, and it does not widen first/prefix
demand into whole-batch observation.

This module places the generic atomic snapshot boundary below that certificate
plus its observer-derived bulk plan.  A successful transaction publishes the
exact reference target, advances the revision, exposes the resource frame, and
marks every batch occurrence executed.  A conflict returns the live snapshot
and complete source account unchanged and retains the exact batch as pending.

The construction applies equally to one foreground task plus compatible
background mind-agents, a physical simulation wave, or any other admitted
cooperative batch.  It is distinct from selecting one alternative world.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.AtomicCertifiedBatchCommit

open Mettapedia.GSLT.Core.AtomicSnapshotTransaction
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl

universe uRevision uItem uGuard uView uState uStateView uAccount

/-! ## Captured batch proposal -/

/-- A certified batch captured at one physical revision.  All other
coordinates remain indexed by the existing `CertifiedBatch`; no target or
resource evidence is copied into editable fields. -/
structure CapturedBatchProposal
    (Revision : Type uRevision)
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {contract : Contract Item Guard View}
    {semantics : ExecutionSemantics Item State StateView}
    {initial referenceTarget : State}
    {demand : Item → Account} {source : Account} {batch : List Item}
    (_certified : CertifiedBatch contract semantics initial referenceTarget
      Account demand source batch) where
  capturedRevision : Revision
  /-- Physical publication of the complete batch requires the observer-derived
  bulk plan; serializability and funding alone do not widen first/prefix
  demand. -/
  bulkAuthorized : (_certified.plan .general).activation = .bulk

/-- Project the atomic transaction interpretation directly from the certified
batch indices. -/
def transactionSpec
    {Revision : Type uRevision}
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {contract : Contract Item Guard View}
    {semantics : ExecutionSemantics Item State StateView}
    {initial referenceTarget : State}
    {demand : Item → Account} {source : Account} {batch : List Item}
    {certified : CertifiedBatch contract semantics initial referenceTarget
      Account demand source batch} :
    Spec Revision State Item (CapturedBatchProposal Revision certified) where
  capturedRevision := CapturedBatchProposal.capturedRevision
  capturedState := fun _proposal => initial
  targetState := fun _proposal => referenceTarget
  pendingWork := fun _proposal => batch

namespace CapturedBatchProposal

variable
    {Revision : Type uRevision}
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {contract : Contract Item Guard View}
    {semantics : ExecutionSemantics Item State StateView}
    {initial referenceTarget : State}
    {demand : Item → Account} {source : Account} {batch : List Item}
    {certified : CertifiedBatch contract semantics initial referenceTarget
      Account demand source batch}
    {proposal : CapturedBatchProposal Revision certified}
    {live : Snapshot Revision State}

/-- Resource inventory after the atomic outcome.  Only commit consumes the
batch demand. -/
def accountAfter : Decision transactionSpec proposal live → Account
  | .committed _ => certified.resources.frame
  | .deferred _ => source

/-- The committed physical target is definitionally the exact certified
reference target. -/
theorem committed_target_exact
    (receipt : CommitReceipt transactionSpec proposal live) :
    (Decision.committed receipt).physicalSnapshot.state = referenceTarget :=
  rfl

/-- The certified additive decomposition becomes the exact physical commit
receipt. -/
theorem committed_account_conservation
    (receipt : CommitReceipt transactionSpec proposal live) :
    source = batchDemand demand batch +
      accountAfter (Decision.committed receipt) :=
  certified.resources.source_eq

/-- Conflict is simultaneous exact rollback of state, resource inventory, and
the complete occurrence batch. -/
theorem deferred_rolls_back_state_account_and_batch
    (conflict : ¬ Matches transactionSpec proposal live) :
    (Decision.deferred conflict).physicalSnapshot = live ∧
      accountAfter (Decision.deferred conflict) = source ∧
      (Decision.deferred conflict).ledger.executed = 0 ∧
      (Decision.deferred conflict).ledger.pending = (batch : Multiset Item) :=
  ⟨rfl, rfl, rfl, rfl⟩

end CapturedBatchProposal

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.Core.ResourceAwareControl.Canary

abbrev Proposal := CapturedBatchProposal Nat completeCertified

def proposal : Proposal :=
  ⟨7, completeCertified.completeBag_dispatches_bulk rfl⟩

abbrev spec : Spec Nat (List Job) Job Proposal :=
  transactionSpec (Revision := Nat) (certified := completeCertified)

def live : Snapshot Nat (List Job) := ⟨7, []⟩

def receipt : CommitReceipt spec proposal live where
  current := ⟨rfl, rfl⟩
  nextRevision := 8
  advanced := by decide

def committed : Decision spec proposal live := .committed receipt

/-- Positive control: the whole certified two-occurrence batch publishes
atomically and consumes its exact linear inventory. -/
theorem complete_batch_commits_atomically :
    committed.physicalSnapshot = ⟨8, [.left, .right]⟩ ∧
      CapturedBatchProposal.accountAfter committed = 0 ∧
      committed.ledger.executed = {.left, .right} ∧
      committed.ledger.pending = 0 := by
  decide

def staleLive : Snapshot Nat (List Job) := ⟨8, []⟩

def staleDecision : Decision spec proposal staleLive :=
  attempt spec proposal staleLive 9 (by decide)

/-- A stale batch cannot partially publish either occurrence or consume any
of its source inventory. -/
theorem stale_batch_rolls_back_whole :
    staleDecision.physicalSnapshot = staleLive ∧
      CapturedBatchProposal.accountAfter staleDecision = inventory ∧
      staleDecision.ledger.executed = 0 ∧
      staleDecision.ledger.pending = {.left, .right} := by
  decide

/-- A first-witness certificate remains controlled and therefore cannot be
captured as a whole-batch atomic publication proposal. -/
theorem first_demand_cannot_authorize_whole_batch :
    ¬ Nonempty (CapturedBatchProposal Nat firstCertified) := by
  rintro ⟨proposal⟩
  have controlled := firstCertified.first_remains_controlled rfl
  have impossible := controlled.symm.trans proposal.bulkAuthorized
  cases impossible

end Canary

#print axioms CapturedBatchProposal.committed_target_exact
#print axioms CapturedBatchProposal.committed_account_conservation
#print axioms CapturedBatchProposal.deferred_rolls_back_state_account_and_batch
#print axioms Canary.complete_batch_commits_atomically
#print axioms Canary.stale_batch_rolls_back_whole
#print axioms Canary.first_demand_cannot_authorize_whole_batch

end Mettapedia.GSLT.Core.AtomicCertifiedBatchCommit
