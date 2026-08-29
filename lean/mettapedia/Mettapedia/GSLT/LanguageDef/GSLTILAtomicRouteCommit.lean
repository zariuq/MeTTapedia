import Mettapedia.GSLT.Core.AtomicSnapshotTransaction
import Mettapedia.GSLT.LanguageDef.GSLTILFundedRouteWaveCommit

/-!
# Atomic snapshot realization of funded GSLT-IL route commits

This module instantiates the policy-neutral atomic transaction kernel with
exact retained-route receipts.  A proposal contains a certified speculative
wave, one selected authorized commit from that wave, an exact selected-route
purse, and the revision at which the common parent was captured.

The transaction specification contains no duplicate target implementation:
its parent, target, and pending work are projections of the route receipts.
Exact snapshot validation then either publishes the whole selected target at
a fresh revision or returns the live snapshot and engine purse unchanged with
the selected occurrences still pending.

Concurrent siblings derived from one snapshot cannot both pass this boundary.
After one commits, the generic revision theorem rejects the other.  Retry,
serial fallback, compatible merge, and permanent rejection remain authored
controllers over that deferred result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.AtomicRouteCommit

open Mettapedia.GSLT.Core.AtomicSnapshotTransaction
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers
open Mettapedia.GSLT.LanguageDef.GSLTIL.ContextualDeltaRouteBridge
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge
open Mettapedia.GSLT.LanguageDef.GSLTIL.FundedContextualCommit
open Mettapedia.GSLT.LanguageDef.GSLTIL.FundedRouteWaveCommit
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteFootprintWaveAdmission
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

universe u

/-! ## Revision-captured route proposals -/

/-- One physical proposal retains the semantic commit as a dependent field.
Its target and pending route therefore cannot disagree with the funded wave
receipt that justifies them. -/
structure CapturedRouteCommit
    (Revision : Type u)
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location Atom Delta Answer Intent Guard CandidateView
      StateView WaveAccount CommitAccount : Type u}
    [DecidableEq Location] [AddMonoid WaveAccount] [AddMonoid CommitAccount]
    {source : theory.World}
    {algebra : DeltaAlgebra (Network Location Atom) Delta}
    {effects : RouteEffectDisplay Occurrence Delta Intent}
    {footprints : RouteFootprintDisplay Occurrence Location}
    {family : RouteFamily theory Occurrence (Network Location Atom) Answer source}
    {pair : IndependentPair algebra effects footprints family}
    {contract : Contract (RouteCandidate theory Occurrence Answer source)
      Guard CandidateView}
    {observeState : Network Location Atom → StateView}
    {waveDemand : RouteCandidate theory Occurrence Answer source → WaveAccount}
    {waveSource : WaveAccount}
    (wave : CertifiedBatch contract
      (IndependentPair.executionSemantics
        (algebra := algebra) (effects := effects) observeState)
      family.parent pair.referenceTarget WaveAccount waveDemand waveSource
      pair.batch)
    (policy : CommitPolicy (RouteCandidate theory Occurrence Answer source))
    (commitCostAt : Occurrence → CommitAccount)
    (commitSource : CommitAccount) where
  capturedRevision : Revision
  commit : StateCommit algebra effects family policy
  receipt : CertifiedRouteWaveCommit wave commitCostAt commitSource commit

/-- The atomic transaction reads every semantic coordinate directly from the
captured route proposal. -/
def routeTransactionSpec
    {Revision : Type u}
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location Atom Delta Answer Intent Guard CandidateView
      StateView WaveAccount CommitAccount : Type u}
    [DecidableEq Location] [AddMonoid WaveAccount] [AddMonoid CommitAccount]
    {source : theory.World}
    {algebra : DeltaAlgebra (Network Location Atom) Delta}
    {effects : RouteEffectDisplay Occurrence Delta Intent}
    {footprints : RouteFootprintDisplay Occurrence Location}
    {family : RouteFamily theory Occurrence (Network Location Atom) Answer source}
    {pair : IndependentPair algebra effects footprints family}
    {contract : Contract (RouteCandidate theory Occurrence Answer source)
      Guard CandidateView}
    {observeState : Network Location Atom → StateView}
    {waveDemand : RouteCandidate theory Occurrence Answer source → WaveAccount}
    {waveSource : WaveAccount}
    {wave : CertifiedBatch contract
      (IndependentPair.executionSemantics
        (algebra := algebra) (effects := effects) observeState)
      family.parent pair.referenceTarget WaveAccount waveDemand waveSource
      pair.batch}
    {policy : CommitPolicy (RouteCandidate theory Occurrence Answer source)}
    {commitCostAt : Occurrence → CommitAccount}
    {commitSource : CommitAccount} :
    Spec Revision (Network Location Atom) Occurrence
      (CapturedRouteCommit Revision wave policy commitCostAt commitSource) where
  capturedRevision := CapturedRouteCommit.capturedRevision
  capturedState := fun _proposal => family.parent
  targetState := fun proposal => proposal.receipt.physicalTarget
  pendingWork := fun proposal =>
    proposal.commit.selection.candidate.route.occurrences

namespace CapturedRouteCommit

variable
    {Revision : Type u}
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location Atom Delta Answer Intent Guard CandidateView
      StateView WaveAccount CommitAccount : Type u}
    [DecidableEq Location] [AddMonoid WaveAccount] [AddMonoid CommitAccount]
    {source : theory.World}
    {algebra : DeltaAlgebra (Network Location Atom) Delta}
    {effects : RouteEffectDisplay Occurrence Delta Intent}
    {footprints : RouteFootprintDisplay Occurrence Location}
    {family : RouteFamily theory Occurrence (Network Location Atom) Answer source}
    {pair : IndependentPair algebra effects footprints family}
    {contract : Contract (RouteCandidate theory Occurrence Answer source)
      Guard CandidateView}
    {observeState : Network Location Atom → StateView}
    {waveDemand : RouteCandidate theory Occurrence Answer source → WaveAccount}
    {waveSource : WaveAccount}
    {wave : CertifiedBatch contract
      (IndependentPair.executionSemantics
        (algebra := algebra) (effects := effects) observeState)
      family.parent pair.referenceTarget WaveAccount waveDemand waveSource
      pair.batch}
    {policy : CommitPolicy (RouteCandidate theory Occurrence Answer source)}
    {commitCostAt : Occurrence → CommitAccount}
    {commitSource : CommitAccount}
    {proposal : CapturedRouteCommit Revision wave policy commitCostAt commitSource}
    {live : Snapshot Revision (Network Location Atom)}

/-- The commit account after an atomic decision.  Conflict spends nothing;
success exposes exactly the residual purse from the funded route receipt. -/
def accountAfter :
    Decision routeTransactionSpec proposal live → CommitAccount
  | .committed _ => proposal.receipt.funding.remaining
  | .deferred _ => commitSource

@[simp] theorem deferred_preserves_account
    (conflict : ¬ Matches routeTransactionSpec proposal live) :
    accountAfter (Decision.deferred conflict) = commitSource :=
  rfl

/-- A successful physical decision publishes exactly the selected candidate
transformer from the speculative wave. -/
theorem committed_state_is_selected_wave_step
    (atomic : CommitReceipt routeTransactionSpec proposal live) :
    (Decision.committed atomic).physicalSnapshot.state =
      candidateStep algebra effects family.parent
        proposal.commit.selection.candidate := by
  exact proposal.receipt.physicalTarget_is_selected_wave_step

/-- Successful publication consumes exactly the selected-route purse and
retains the untouched frame. -/
theorem committed_account_conservation
    (atomic : CommitReceipt routeTransactionSpec proposal live) :
    commitSource = proposal.receipt.funding.spent +
      accountAfter (Decision.committed atomic) :=
  proposal.receipt.commit_purse_conserved

/-- Conflict is exact rollback simultaneously for ambient state, account, and
the selected physical occurrence route. -/
theorem deferred_rolls_back_state_account_and_work
    (conflict : ¬ Matches routeTransactionSpec proposal live) :
    (Decision.deferred conflict).physicalSnapshot = live ∧
      accountAfter (Decision.deferred conflict) = commitSource ∧
      (Decision.deferred conflict).ledger.pending =
        (proposal.commit.selection.candidate.route.occurrences :
          Multiset Occurrence) :=
  ⟨rfl, rfl, rfl⟩

end CapturedRouteCommit

/-! ## Positive and adversarial controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteFootprintWaveAdmission.Canary
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge.Canary

def allowBoth : CommitPolicy
    (RouteCandidate collisionTheory Nat Bool ()) where
  Allows candidate := candidate = leftCandidate ∨ candidate = rightCandidate

def leftSelection : Selection family.candidates where
  index := 0
  candidate := leftCandidate
  selected := rfl

def rightSelection : Selection family.candidates where
  index := 1
  candidate := rightCandidate
  selected := rfl

def leftAuthorization : AuthorizedSelection allowBoth leftSelection where
  allowed := Or.inl rfl

def rightAuthorization : AuthorizedSelection allowBoth rightSelection where
  allowed := Or.inr rfl

def leftCommit : StateCommit networkAlgebra effects family allowBoth :=
  commitState networkAlgebra effects family allowBoth leftSelection
    leftAuthorization

def rightCommit : StateCommit networkAlgebra effects family allowBoth :=
  commitState networkAlgebra effects family allowBoth rightSelection
    rightAuthorization

def commitCostAt (_occurrence : Nat) : Nat := 1

def fundedLeft : FundedStateCommit commitCostAt 1 leftCommit where
  funding :=
    { frame := 0
      source_eq := by decide }

def fundedRight : FundedStateCommit commitCostAt 1 rightCommit where
  funding :=
    { frame := 0
      source_eq := by decide }

def leftWaveCommit : CertifiedRouteWaveCommit certified commitCostAt 1 leftCommit where
  selectedInWave := by
    change leftCandidate ∈ [leftCandidate, rightCandidate]
    simp
  funding := fundedLeft

def rightWaveCommit : CertifiedRouteWaveCommit certified commitCostAt 1 rightCommit where
  selectedInWave := by
    change rightCandidate ∈ [leftCandidate, rightCandidate]
    simp
  funding := fundedRight

abbrev Proposal :=
  CapturedRouteCommit Nat certified allowBoth commitCostAt 1

def leftProposal : Proposal where
  capturedRevision := 7
  commit := leftCommit
  receipt := leftWaveCommit

def rightProposal : Proposal where
  capturedRevision := 7
  commit := rightCommit
  receipt := rightWaveCommit

abbrev routeSpec : Spec Nat TestState Nat Proposal :=
  routeTransactionSpec (Revision := Nat) (wave := certified)
    (policy := allowBoth) (commitCostAt := commitCostAt) (commitSource := 1)

def live : Snapshot Nat TestState := ⟨7, family.parent⟩

def leftAtomic : CommitReceipt routeSpec leftProposal live where
  current := ⟨rfl, rfl⟩
  nextRevision := 8
  advanced := by decide

def committedLeft : Decision routeSpec leftProposal live :=
  .committed leftAtomic

/-- Positive control: the atomic receipt publishes exactly the selected left
state, advances the revision, spends one unit, and accounts for occurrence
zero exactly once. -/
theorem selected_route_commit_is_atomic_and_conservative :
    committedLeft.physicalSnapshot.revision = 8 ∧
      committedLeft.physicalSnapshot.state false = {()} ∧
      committedLeft.physicalSnapshot.state true = ∅ ∧
      CapturedRouteCommit.accountAfter committedLeft = 0 ∧
      committedLeft.ledger.executed = {0} := by
  decide

/-- The right alternative was explored and funded, but the left commit's
revision advance makes the old right proposal stale. -/
theorem committed_left_rejects_captured_right :
    ¬ Matches routeSpec rightProposal leftAtomic.after :=
  leftAtomic.after_rejects_same_revision_sibling rfl

def deferredRight : Decision routeSpec rightProposal leftAtomic.after :=
  attempt routeSpec rightProposal leftAtomic.after 9 (by decide)

/-- A losing race is not a partial second commit: the left state and revision
remain exact, the right purse is untouched, and occurrence one stays pending. -/
theorem stale_sibling_is_exactly_deferred :
    deferredRight.physicalSnapshot = leftAtomic.after ∧
      CapturedRouteCommit.accountAfter deferredRight = 1 ∧
      deferredRight.ledger.executed = 0 ∧
      deferredRight.ledger.pending = {1} := by
  decide

def noIntents : IntentPolicy Bool where
  Allows _ := False

/-- Atomic state publication still does not authorize the selected route's
deferred external intent. -/
theorem atomic_commit_does_not_execute_intents :
    Nonempty (CommitReceipt routeSpec leftProposal live) ∧
      ¬ Nonempty (AuthorizedIntents noIntents leftCommit) := by
  constructor
  · exact ⟨leftAtomic⟩
  · rintro ⟨authorization⟩
    exact authorization.allowed

end Canary

#print axioms CapturedRouteCommit.committed_state_is_selected_wave_step
#print axioms CapturedRouteCommit.committed_account_conservation
#print axioms CapturedRouteCommit.deferred_rolls_back_state_account_and_work
#print axioms Canary.selected_route_commit_is_atomic_and_conservative
#print axioms Canary.committed_left_rejects_captured_right
#print axioms Canary.stale_sibling_is_exactly_deferred
#print axioms Canary.atomic_commit_does_not_execute_intents

end Mettapedia.GSLT.LanguageDef.GSLTIL.AtomicRouteCommit
