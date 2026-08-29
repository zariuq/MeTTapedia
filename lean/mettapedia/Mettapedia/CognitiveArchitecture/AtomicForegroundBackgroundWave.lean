import Mettapedia.CognitiveArchitecture.ForegroundBackgroundParallelWave
import Mettapedia.GSLT.Core.AtomicCertifiedBatchFamily

/-!
# Atomic foreground/background mind-agent wave

The real foreground chaining step and background premise-index refresh already
form a certified, STI/LTI-funded wave.  This module carries that exact batch
through the generic atomic snapshot boundary.

On success, the continuation-store step and premise-index refresh become
visible together at one fresh revision and consume their exact paired attention
account.  On conflict, neither update becomes visible, both attention accounts
remain untouched, and both work occurrences stay pending.  The intrusive
background rewinder cannot enter this boundary because it never earned the
underlying certified batch.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.AtomicForegroundBackgroundWave

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.CognitiveArchitecture.AttentionEconomyResourceControl
open Mettapedia.CognitiveArchitecture.ForegroundBackgroundParallelWave
open Mettapedia.CognitiveArchitecture.ForegroundChainingActivationPolicy
open Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService
open Mettapedia.GSLT.Core.AtomicCertifiedBatchCommit
open Mettapedia.GSLT.Core.AtomicCertifiedBatchFamily
open Mettapedia.GSLT.Core.AtomicSnapshotTransaction
open Mettapedia.GSLT.Core.ResourceAwareControl

noncomputable section

abbrev Proposal := CapturedBatchProposal Nat certified

def proposal : Proposal :=
  { capturedRevision := 11
    bulkAuthorized := wave.completeBag_dispatches_bulk rfl }

abbrev spec : Spec Nat Workspace Work Proposal :=
  transactionSpec (Revision := Nat) (certified := certified)

def live : Snapshot Nat Workspace := ⟨11, initialWorkspace⟩

def receipt : CommitReceipt spec proposal live where
  current := ⟨rfl, rfl⟩
  nextRevision := 12
  advanced := by decide

def committed : Decision spec proposal live := .committed receipt

/-- The useful foreground and background operations cross the physical
boundary as one complete revision while retaining their two cognitive roles
and exact paired attention account. -/
theorem foreground_and_background_commit_together :
    (wave.certified.plan .general).activation = .bulk ∧
      committed.physicalSnapshot = ⟨12, parallelTarget⟩ ∧
      committed.physicalSnapshot.state.1 = afterBridge ∧
      committed.physicalSnapshot.state.2 = selectedPremises ∧
      CapturedBatchProposal.accountAfter committed = 0 ∧
      committed.ledger.executed =
        ({.foregroundBridge, .refreshPremiseIndex} : Multiset Work) ∧
      role ⟨0, by decide⟩ = .foreground ∧
      role ⟨1, by decide⟩ = .background := by
  refine ⟨wave.completeBag_dispatches_bulk rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · decide
  · decide

/-- Both typed attention instruments obey their already-proved exact
decomposition at the physical commit boundary. -/
theorem paired_attention_is_conserved_at_commit :
    (shortSource, longSource) =
      batchDemand (fun work => (shortDemand work, longDemand work))
          parallelBatch +
        CapturedBatchProposal.accountAfter committed :=
  CapturedBatchProposal.committed_account_conservation receipt

def staleLive : Snapshot Nat Workspace := ⟨12, initialWorkspace⟩

def staleConflict : ¬ Matches spec proposal staleLive := by
  intro current
  have revisionImpossible := current.revision_eq
  norm_num [staleLive, spec,
    Mettapedia.GSLT.Core.AtomicCertifiedBatchCommit.transactionSpec,
    proposal] at revisionImpossible

def staleDecision : Decision spec proposal staleLive :=
  .deferred staleConflict

/-- A stale cooperative wave is an exact all-or-nothing rollback.  Neither the
foreground step nor the background refresh partially appears; both STI/LTI
sources and both work occurrences remain available. -/
theorem stale_wave_rolls_back_state_attention_and_work :
    staleDecision.physicalSnapshot = staleLive ∧
      CapturedBatchProposal.accountAfter staleDecision =
        (shortSource, longSource) ∧
      staleDecision.ledger.executed = 0 ∧
      staleDecision.ledger.pending =
        ({.foregroundBridge, .refreshPremiseIndex} : Multiset Work) := by
  rcases
      CapturedBatchProposal.deferred_rolls_back_state_account_and_batch
        (certified := certified) (proposal := proposal) (live := staleLive)
        staleConflict with
    ⟨stateRollback, accountRollback, executedRollback, pendingRollback⟩
  refine ⟨stateRollback, accountRollback, executedRollback, ?_⟩
  exact pendingRollback.trans rfl

/-! ## Fresh certification of the real cognitive workspace -/

def foregroundFamily :
    BulkCertifiedBatchFamily completeBagContract semantics
      (ImportanceAccount Agent Nat)
      (fun work => (shortDemand work, longDemand work))
      (shortSource, longSource) parallelBatch where
  targetAt := parallelTargetAt
  certifiedAt := certifiedAt
  bulkAuthorizedAt source :=
    (certifiedAt source).completeBag_dispatches_bulk rfl

/-- An intervening foreground transition changes the complete physical parent
of the old proposal. -/
def interveningWorkspace : Workspace :=
  (afterBridge, ∅)

def interveningLive : Snapshot Nat Workspace :=
  ⟨13, interveningWorkspace⟩

def oldProposalConflict : ¬ Matches spec proposal interveningLive := by
  intro current
  have revisionImpossible := current.revision_eq
  norm_num [interveningLive, spec,
    Mettapedia.GSLT.Core.AtomicCertifiedBatchCommit.transactionSpec,
    proposal] at revisionImpossible

abbrev FamilyProposal := CapturedFamilyProposal Nat foregroundFamily

def freshProposal : FamilyProposal :=
  captureLive (family := foregroundFamily) interveningLive

abbrev familySpec : Spec Nat Workspace Work FamilyProposal :=
  Mettapedia.GSLT.Core.AtomicCertifiedBatchFamily.transactionSpec
    (Revision := Nat) (family := foregroundFamily)

def freshReceipt : CommitReceipt familySpec freshProposal interveningLive where
  current := captureLive_matches (family := foregroundFamily) interveningLive
  nextRevision := 14
  advanced := by decide

def freshCommitted : Decision familySpec freshProposal interveningLive :=
  .committed freshReceipt

/-- The stale proposal remains invalid.  A fresh certificate at the complete
intervening cognitive state can publish exactly one new foreground/indexer
wave without spending the stale attempt's attention account. -/
theorem real_workspace_retry_requires_fresh_certificate :
    ¬ Matches spec proposal interveningLive ∧
      Matches familySpec freshProposal interveningLive ∧
      freshCommitted.physicalSnapshot =
        ⟨14, parallelTargetAt interveningWorkspace⟩ ∧
      Mettapedia.GSLT.Core.AtomicCertifiedBatchFamily.CapturedFamilyProposal.accountAfter
          freshCommitted = 0 ∧
      freshCommitted.ledger.executed =
        ({.foregroundBridge, .refreshPremiseIndex} : Multiset Work) := by
  exact ⟨oldProposalConflict,
    captureLive_matches (family := foregroundFamily) interveningLive,
    rfl, rfl, rfl⟩

abbrev IntrusiveCertified :=
  CertifiedBatch completeBagContract semantics initialWorkspace
    intrusiveReferenceTarget (Nat × Nat) laneDemand (1, 1) intrusiveBatch

/-- Exact lane resources do not let the foreground-writing organizer enter an
atomic wave: it first has to earn observer serializability, which it cannot. -/
theorem intrusive_organizer_cannot_enter_atomic_boundary :
    Nonempty
        (BatchSeparation (Nat × Nat) laneDemand (1, 1) intrusiveBatch) ∧
      ¬ Nonempty
        (Σ certifiedIntrusive : IntrusiveCertified,
          CapturedBatchProposal Nat certifiedIntrusive) := by
  constructor
  · exact resources_do_not_grant_intrusive_wave.1
  · rintro ⟨certifiedIntrusive, _proposal⟩
    exact resources_do_not_grant_intrusive_wave.2 ⟨certifiedIntrusive⟩

#print axioms foreground_and_background_commit_together
#print axioms paired_attention_is_conserved_at_commit
#print axioms stale_wave_rolls_back_state_attention_and_work
#print axioms real_workspace_retry_requires_fresh_certificate
#print axioms intrusive_organizer_cannot_enter_atomic_boundary

end

end Mettapedia.CognitiveArchitecture.AtomicForegroundBackgroundWave
