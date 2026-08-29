import Mettapedia.GSLT.Core.ResourceAwareControl

/-!
# Policy-neutral atomic snapshot transactions

This module isolates the common transaction law beneath speculative
evaluation, optimizer trials, space overlays, and revision-scoped execution.
A proposal names the snapshot it was derived from, its exact target state, and
the work occurrences represented by the proposal.  A physical commit is
permitted only when both the live revision and the live state still match that
captured snapshot.

The result is deliberately small:

* a successful receipt atomically exposes the complete target at a fresh
  revision;
* a conflict exposes the live snapshot unchanged and retains all work as
  pending; and
* every accepted commit makes proposals derived from the old revision stale.

Retry, serial fallback, compatible merge, and rejection are policies over the
deferred constructor.  They are not built into this transaction boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.AtomicSnapshotTransaction

open Mettapedia.GSLT.Core.ResourceAwareControl

universe uRevision uState uWork uProposal

/-! ## Captured and live state -/

/-- A complete physical snapshot.  The state is retained alongside the
revision so a backend cannot silently rely on an unsound revision discipline. -/
structure Snapshot (Revision : Type uRevision) (State : Type uState) where
  revision : Revision
  state : State
deriving DecidableEq, Repr

/-- The semantic interpretation of a proposal.  Proposal evidence lives in
the proposal type; this record only states how the atomic layer reads its
captured revision, captured parent, complete target, and retained work. -/
structure Spec (Revision : Type uRevision) (State : Type uState)
    (Work : Type uWork) (Proposal : Type uProposal) where
  capturedRevision : Proposal → Revision
  capturedState : Proposal → State
  targetState : Proposal → State
  pendingWork : Proposal → List Work

def Spec.captured
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    (spec : Spec Revision State Work Proposal) (proposal : Proposal) :
    Snapshot Revision State :=
  ⟨spec.capturedRevision proposal, spec.capturedState proposal⟩

/-- Exact optimistic validation.  Matching only the revision is insufficient:
the live state must also equal the captured parent. -/
structure Matches
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    (spec : Spec Revision State Work Proposal)
    (proposal : Proposal) (live : Snapshot Revision State) : Prop where
  revision_eq : live.revision = spec.capturedRevision proposal
  state_eq : live.state = spec.capturedState proposal

theorem captured_matches
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    (spec : Spec Revision State Work Proposal) (proposal : Proposal) :
    Matches spec proposal (spec.captured proposal) :=
  ⟨rfl, rfl⟩

/-! ## Atomic commit and exact deferral -/

/-- A successful atomic commit.  The semantic target is read directly from
the proposal, while the fresh revision is retained as an explicit receipt. -/
structure CommitReceipt
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    (spec : Spec Revision State Work Proposal)
    (proposal : Proposal) (live : Snapshot Revision State) where
  current : Matches spec proposal live
  nextRevision : Revision
  advanced : nextRevision ≠ live.revision

def CommitReceipt.after
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    {spec : Spec Revision State Work Proposal}
    {proposal : Proposal} {live : Snapshot Revision State}
    (receipt : CommitReceipt spec proposal live) : Snapshot Revision State :=
  ⟨receipt.nextRevision, spec.targetState proposal⟩

/-- The atomic boundary has exactly two semantic outcomes.  A conflict proof
does not choose what a later controller will do with the pending proposal. -/
inductive Decision
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    (spec : Spec Revision State Work Proposal)
    (proposal : Proposal) (live : Snapshot Revision State) where
  | committed (receipt : CommitReceipt spec proposal live)
  | deferred (conflict : ¬ Matches spec proposal live)

/-- The executable exact validator.  It accepts only equality of the complete
captured snapshot and otherwise returns the proof-relevant deferred branch. -/
def attempt
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    [DecidableEq Revision] [DecidableEq State]
    (spec : Spec Revision State Work Proposal)
    (proposal : Proposal) (live : Snapshot Revision State)
    (nextRevision : Revision) (advanced : nextRevision ≠ live.revision) :
    Decision spec proposal live :=
  if revisionMatches : live.revision = spec.capturedRevision proposal then
    if stateMatches : live.state = spec.capturedState proposal then
      .committed
        { current := ⟨revisionMatches, stateMatches⟩
          nextRevision := nextRevision
          advanced := advanced }
    else
      .deferred fun current => stateMatches current.state_eq
  else
    .deferred fun current => revisionMatches current.revision_eq

namespace Decision

variable
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    {spec : Spec Revision State Work Proposal}
    {proposal : Proposal} {live : Snapshot Revision State}

/-- Atomicity: a commit exposes the complete proposal target, while deferral
returns the live snapshot exactly. -/
def physicalSnapshot : Decision spec proposal live → Snapshot Revision State
  | .committed receipt => receipt.after
  | .deferred _ => live

/-- Occurrence ledger for the complete proposal.  No work position can vanish
at the transaction boundary. -/
def ledger (decision : Decision spec proposal live) :
    FundingDecision.Ledger Work :=
  match decision with
  | .committed _ => ⟨(spec.pendingWork proposal : Multiset Work), 0⟩
  | .deferred _ => ⟨0, (spec.pendingWork proposal : Multiset Work)⟩

/-- The position-preserving form of the same all-or-nothing work receipt.
Candidate observers may lawfully forget order, but FIFO and age-sensitive
retry controllers must not reconstruct it from a multiset. -/
structure OrderedLedger (Work : Type uWork) where
  executed : List Work
  pending : List Work
deriving Repr

def orderedLedger (decision : Decision spec proposal live) :
    OrderedLedger Work :=
  match decision with
  | .committed _ => ⟨spec.pendingWork proposal, []⟩
  | .deferred _ => ⟨[], spec.pendingWork proposal⟩

/-- Forgetting position from the ordered receipt recovers exactly the existing
multiset receipt, coordinate by coordinate. -/
theorem orderedLedger_erases_to_ledger
    (decision : Decision spec proposal live) :
    (decision.orderedLedger.executed : Multiset Work) =
        decision.ledger.executed ∧
      (decision.orderedLedger.pending : Multiset Work) =
        decision.ledger.pending := by
  cases decision <;> exact ⟨rfl, rfl⟩

/-- Atomicity also accounts for the exact authored list: one side is complete
and the other is empty. -/
theorem orderedLedger_accounts
    (decision : Decision spec proposal live) :
    decision.orderedLedger.executed ++ decision.orderedLedger.pending =
      spec.pendingWork proposal := by
  cases decision <;> simp [orderedLedger]

theorem ledger_accounts (decision : Decision spec proposal live) :
    decision.ledger.executed + decision.ledger.pending =
      (spec.pendingWork proposal : Multiset Work) := by
  cases decision <;> simp [ledger]

@[simp] theorem committed_physical_snapshot
    (receipt : CommitReceipt spec proposal live) :
    physicalSnapshot (Decision.committed receipt) = receipt.after :=
  rfl

@[simp] theorem deferred_is_exact_rollback
    (conflict : ¬ Matches spec proposal live) :
    physicalSnapshot (Decision.deferred conflict) = live :=
  rfl

@[simp] theorem committed_executes_exact_work
    (receipt : CommitReceipt spec proposal live) :
    (Decision.committed receipt).ledger.executed =
      (spec.pendingWork proposal : Multiset Work) :=
  rfl

@[simp] theorem committed_executes_exact_ordered_work
    (receipt : CommitReceipt spec proposal live) :
    (Decision.committed receipt).orderedLedger.executed =
      spec.pendingWork proposal :=
  rfl

@[simp] theorem deferred_retains_exact_work
    (conflict : ¬ Matches spec proposal live) :
    (Decision.deferred conflict).ledger.pending =
      (spec.pendingWork proposal : Multiset Work) :=
  rfl

@[simp] theorem deferred_retains_exact_ordered_work
    (conflict : ¬ Matches spec proposal live) :
    (Decision.deferred conflict).orderedLedger.pending =
      spec.pendingWork proposal :=
  rfl

end Decision

namespace CommitReceipt

variable
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    {spec : Spec Revision State Work Proposal}
    {proposal : Proposal} {live : Snapshot Revision State}

/-- A successful revision advance makes the same captured proposal stale. -/
theorem after_rejects_same_proposal
    (receipt : CommitReceipt spec proposal live) :
    ¬ Matches spec proposal receipt.after := by
  intro currentAfter
  apply receipt.advanced
  calc
    receipt.nextRevision = spec.capturedRevision proposal :=
      currentAfter.revision_eq
    _ = live.revision := receipt.current.revision_eq.symm

/-- A sibling derived from the same captured revision is also stale after one
commit.  It may be retried only by producing a new proposal or by an authored
merge/fallback policy that earns a different receipt. -/
theorem after_rejects_same_revision_sibling
    (receipt : CommitReceipt spec proposal live)
    {sibling : Proposal}
    (sameRevision :
      spec.capturedRevision sibling = spec.capturedRevision proposal) :
    ¬ Matches spec sibling receipt.after := by
  intro currentAfter
  apply receipt.advanced
  calc
    receipt.nextRevision = spec.capturedRevision sibling :=
      currentAfter.revision_eq
    _ = spec.capturedRevision proposal := sameRevision
    _ = live.revision := receipt.current.revision_eq.symm

end CommitReceipt

/-! ## Positive and negative controls -/

namespace Canary

inductive Proposal where
  | left
  | right
deriving DecidableEq, Repr

def spec : Spec Nat Nat Proposal Proposal where
  capturedRevision _ := 7
  capturedState _ := 10
  targetState
    | .left => 11
    | .right => 12
  pendingWork proposal := [proposal]

def live : Snapshot Nat Nat := ⟨7, 10⟩

def leftReceipt : CommitReceipt spec .left live where
  current := ⟨rfl, rfl⟩
  nextRevision := 8
  advanced := by decide

def committedLeft : Decision spec .left live :=
  .committed leftReceipt

/-- Positive control: an exact current proposal commits its complete target at
the fresh revision and accounts for its occurrence once. -/
theorem current_commit_is_atomic :
    committedLeft.physicalSnapshot = ⟨8, 11⟩ ∧
      committedLeft.ledger.executed = {.left} ∧
      committedLeft.ledger.pending = 0 := by
  decide

def staleLive : Snapshot Nat Nat := ⟨8, 10⟩

def staleDecision : Decision spec .left staleLive :=
  attempt spec .left staleLive 9 (by decide)

/-- A changed revision rolls back exactly even when the state payload still
equals the captured state. -/
theorem changed_revision_is_exact_rollback :
    staleDecision.physicalSnapshot = staleLive ∧
      staleDecision.ledger.executed = 0 ∧
      staleDecision.ledger.pending = {.left} := by
  decide

def changedStateLive : Snapshot Nat Nat := ⟨7, 99⟩

def changedStateDecision : Decision spec .left changedStateLive :=
  attempt spec .left changedStateLive 8 (by decide)

/-- Matching revision alone is not enough: an unexplained state change also
forces exact rollback and preserves the work occurrence. -/
theorem changed_state_is_exact_rollback :
    changedStateDecision.physicalSnapshot = changedStateLive ∧
      changedStateDecision.ledger.executed = 0 ∧
      changedStateDecision.ledger.pending = {.left} := by
  decide

/-- Once the left proposal commits, the right proposal captured from the same
snapshot cannot race into the successor without revalidation. -/
theorem committed_revision_rejects_sibling :
    ¬ Matches spec .right leftReceipt.after :=
  leftReceipt.after_rejects_same_revision_sibling rfl

/-- Multiset accounting preserves multiplicity but cannot reconstruct authored
retry order; the ordered ledger therefore carries genuine extra information. -/
theorem bag_receipt_does_not_recover_authored_order :
    ([Proposal.left, Proposal.right] : Multiset Proposal) =
        ([Proposal.right, Proposal.left] : Multiset Proposal) ∧
      ([Proposal.left, Proposal.right] : List Proposal) ≠
        [Proposal.right, Proposal.left] := by
  decide

end Canary

#print axioms captured_matches
#print axioms Decision.ledger_accounts
#print axioms Decision.orderedLedger_erases_to_ledger
#print axioms Decision.orderedLedger_accounts
#print axioms Decision.deferred_is_exact_rollback
#print axioms CommitReceipt.after_rejects_same_proposal
#print axioms CommitReceipt.after_rejects_same_revision_sibling
#print axioms Canary.current_commit_is_atomic
#print axioms Canary.changed_revision_is_exact_rollback
#print axioms Canary.changed_state_is_exact_rollback
#print axioms Canary.committed_revision_rejects_sibling
#print axioms Canary.bag_receipt_does_not_recover_authored_order

end Mettapedia.GSLT.Core.AtomicSnapshotTransaction
