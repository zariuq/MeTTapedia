import Mettapedia.GSLT.Core.AtomicCertifiedBatchCommit

/-!
# State-indexed atomic certified batches

A stale proposal cannot be retried merely by changing its revision.  The
batch must be certified again at the current physical state, and the declared
observer must still authorize publication of the complete batch.

This module packages that stronger, source-parametric authority.  A bulk
certified family supplies an exact target and a certified batch for every
captured source state.  Capturing the live snapshot then produces a fresh
proposal whose semantic evidence is indexed by that exact state.  The
transaction boundary remains policy-neutral: it does not decide when a
controller should refresh or how often a deferred proposal should be retried.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.AtomicCertifiedBatchFamily

open Mettapedia.GSLT.Core.AtomicCertifiedBatchCommit
open Mettapedia.GSLT.Core.AtomicSnapshotTransaction
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl

universe uRevision uItem uGuard uView uState uStateView uAccount

/-! ## Source-parametric certification -/

/-- An exact complete-batch certificate at every source state, together with
the observer-derived authority to publish the whole batch at each source. -/
structure BulkCertifiedBatchFamily
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {State : Type uState} {StateView : Type uStateView}
    (contract : Contract Item Guard View)
    (semantics : ExecutionSemantics Item State StateView)
    (Account : Type uAccount) [AddMonoid Account]
    (demand : Item → Account) (source : Account) (batch : List Item) where
  targetAt : State → State
  certifiedAt : ∀ initial,
    CertifiedBatch contract semantics initial (targetAt initial)
      Account demand source batch
  bulkAuthorizedAt : ∀ initial,
    ((certifiedAt initial).plan .general).activation = .bulk

/-- A family proposal retains exactly the physical snapshot at which the
state-indexed certificate was constructed. -/
structure CapturedFamilyProposal
    (Revision : Type uRevision)
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {contract : Contract Item Guard View}
    {semantics : ExecutionSemantics Item State StateView}
    {demand : Item → Account} {source : Account} {batch : List Item}
    (_family : BulkCertifiedBatchFamily contract semantics Account demand
      source batch) where
  captured : Snapshot Revision State

/-- Read the policy-neutral transaction coordinates from the captured live
state and its source-indexed certified family. -/
def transactionSpec
    {Revision : Type uRevision}
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {contract : Contract Item Guard View}
    {semantics : ExecutionSemantics Item State StateView}
    {demand : Item → Account} {source : Account} {batch : List Item}
    {family : BulkCertifiedBatchFamily contract semantics Account demand
      source batch} :
    Spec Revision State Item (CapturedFamilyProposal Revision family) where
  capturedRevision := fun proposal => proposal.captured.revision
  capturedState := fun proposal => proposal.captured.state
  targetState := fun proposal => family.targetAt proposal.captured.state
  pendingWork := fun _proposal => batch

namespace CapturedFamilyProposal

variable
    {Revision : Type uRevision}
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {contract : Contract Item Guard View}
    {semantics : ExecutionSemantics Item State StateView}
    {demand : Item → Account} {source : Account} {batch : List Item}
    {family : BulkCertifiedBatchFamily contract semantics Account demand
      source batch}
    {proposal : CapturedFamilyProposal Revision family}
    {live : Snapshot Revision State}

/-- The family certificate at the exact captured state can be viewed through
the single-snapshot proposal interface without reconstructing any witness. -/
def toBatchProposal :
    CapturedBatchProposal Revision
      (family.certifiedAt proposal.captured.state) where
  capturedRevision := proposal.captured.revision
  bulkAuthorized := family.bulkAuthorizedAt proposal.captured.state

/-- Resource inventory after a family transaction.  Conflict spends nothing;
success exposes the exact frame of the certificate at the captured state. -/
def accountAfter : Decision transactionSpec proposal live → Account
  | .committed _ =>
      (family.certifiedAt proposal.captured.state).resources.frame
  | .deferred _ => source

/-- Atomic success publishes exactly the target certified at the captured
source state. -/
theorem committed_target_exact
    (receipt : CommitReceipt transactionSpec proposal live) :
    (Decision.committed receipt).physicalSnapshot.state =
      family.targetAt proposal.captured.state :=
  rfl

/-- The source-indexed certificate supplies the exact resource decomposition
at successful publication. -/
theorem committed_account_conservation
    (receipt : CommitReceipt transactionSpec proposal live) :
    source = batchDemand demand batch +
      accountAfter (Decision.committed receipt) :=
  (family.certifiedAt proposal.captured.state).resources.source_eq

/-- Conflict rolls back physical state, resource inventory, and the complete
batch together. -/
theorem deferred_rolls_back_state_account_and_batch
    (conflict : ¬ Matches transactionSpec proposal live) :
    (Decision.deferred conflict).physicalSnapshot = live ∧
      accountAfter (Decision.deferred conflict) = source ∧
      (Decision.deferred conflict).ledger.executed = 0 ∧
      (Decision.deferred conflict).ledger.pending =
        (batch : Multiset Item) :=
  ⟨rfl, rfl, rfl, rfl⟩

end CapturedFamilyProposal

/-! ## Fresh capture -/

/-- Construct a new proposal from the complete live snapshot.  The ability to
do this comes from the source-parametric family certificate, not from a stale
proposal. -/
def captureLive
    {Revision : Type uRevision}
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {contract : Contract Item Guard View}
    {semantics : ExecutionSemantics Item State StateView}
    {demand : Item → Account} {source : Account} {batch : List Item}
    {family : BulkCertifiedBatchFamily contract semantics Account demand
      source batch}
    (live : Snapshot Revision State) :
    CapturedFamilyProposal Revision family :=
  ⟨live⟩

theorem captureLive_matches
    {Revision : Type uRevision}
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {contract : Contract Item Guard View}
    {semantics : ExecutionSemantics Item State StateView}
    {demand : Item → Account} {source : Account} {batch : List Item}
    {family : BulkCertifiedBatchFamily contract semantics Account demand
      source batch}
    (live : Snapshot Revision State) :
    Matches transactionSpec (captureLive (family := family) live) live :=
  ⟨rfl, rfl⟩

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.Core.ResourceAwareControl.Canary

def appendCertifiedAt (initial : List Job) :
    CertifiedBatch completeBag appendBagSemantics initial
      (initial ++ [.left, .right]) (Multiset Token) demand inventory
      [.left, .right] where
  nonempty := by decide
  candidateInvariant := bag_permutationInvariant [.left, .right]
  executionSerializable := append_serializes_to_bag initial [.left, .right]
  resources := disjointSeparation

def appendFamily :
    BulkCertifiedBatchFamily completeBag appendBagSemantics
      (Multiset Token) demand inventory [.left, .right] where
  targetAt initial := initial ++ [.left, .right]
  certifiedAt := appendCertifiedAt
  bulkAuthorizedAt initial :=
    (appendCertifiedAt initial).completeBag_dispatches_bulk rfl

abbrev Proposal := CapturedFamilyProposal Nat appendFamily

def oldProposal : Proposal := ⟨⟨7, []⟩⟩

abbrev spec : Spec Nat (List Job) Job Proposal :=
  transactionSpec (Revision := Nat) (family := appendFamily)

def interveningLive : Snapshot Nat (List Job) :=
  ⟨8, [.contested]⟩

def oldConflict : ¬ Matches spec oldProposal interveningLive := by
  intro current
  have revisionImpossible := current.revision_eq
  norm_num [spec, transactionSpec, oldProposal, interveningLive] at revisionImpossible

def oldDeferred : Decision spec oldProposal interveningLive :=
  .deferred oldConflict

def freshProposal : Proposal := captureLive interveningLive

def freshReceipt : CommitReceipt spec freshProposal interveningLive where
  current := captureLive_matches interveningLive
  nextRevision := 9
  advanced := by decide

def freshCommitted : Decision spec freshProposal interveningLive :=
  .committed freshReceipt

/-- A stale proposal remains deferred, while a new certificate indexed by the
complete intervening state may append the exact batch at a fresh revision. -/
theorem stale_does_not_retry_but_fresh_capture_commits :
    oldDeferred.physicalSnapshot = interveningLive ∧
      oldDeferred.ledger.pending = ({.left, .right} : Multiset Job) ∧
      freshCommitted.physicalSnapshot =
        ⟨9, [.contested, .left, .right]⟩ ∧
      CapturedFamilyProposal.accountAfter freshCommitted = 0 ∧
      freshCommitted.ledger.executed =
        ({.left, .right} : Multiset Job) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

abbrev ImpossibleFirstFamily :=
  BulkCertifiedBatchFamily firstWitness appendBagSemantics
    (Multiset Token) demand inventory [.left, .right]

/-- Source-parametric certification cannot smuggle whole-batch authority
through a first-witness observer. -/
theorem first_observation_has_no_bulk_certified_family :
    ¬ Nonempty ImpossibleFirstFamily := by
  rintro ⟨family⟩
  have controlled := (family.certifiedAt []).first_remains_controlled rfl
  have impossible := controlled.symm.trans (family.bulkAuthorizedAt [])
  cases impossible

end Canary

#print axioms CapturedFamilyProposal.committed_target_exact
#print axioms CapturedFamilyProposal.committed_account_conservation
#print axioms CapturedFamilyProposal.deferred_rolls_back_state_account_and_batch
#print axioms captureLive_matches
#print axioms Canary.stale_does_not_retry_but_fresh_capture_commits
#print axioms Canary.first_observation_has_no_bulk_certified_family

end Mettapedia.GSLT.Core.AtomicCertifiedBatchFamily
