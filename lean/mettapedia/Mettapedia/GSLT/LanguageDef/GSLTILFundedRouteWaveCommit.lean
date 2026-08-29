import Mettapedia.GSLT.LanguageDef.GSLTILFundedContextualCommit
import Mettapedia.GSLT.LanguageDef.GSLTILRouteFootprintWaveAdmission

/-!
# Funded selected commits from certified contextual route waves

A certified route wave and a physical commit are different receipts.  The
wave licenses permutation-insensitive execution of an exact candidate batch;
the commit chooses one retained candidate, applies only that candidate's
delta, and consumes an independently typed engine purse.

`CertifiedRouteWaveCommit` is their pullback over candidate membership.  Its
selected candidate must occur in the certified wave, and its commit must be
funded for the exact physical occurrence route selected by the commit
receipt.  The construction does not identify the speculative all-wave target
with the physical selected target, and it leaves external intents deferred.

This is the semantic boundary needed by commit-at-observation.  Snapshot
validation, conflict handling, rollback, and external-intent execution remain
authored physical-space policies rather than hidden consequences of wave
admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.FundedRouteWaveCommit

open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers
open Mettapedia.GSLT.LanguageDef.GSLTIL.ContextualDeltaRouteBridge
open Mettapedia.GSLT.LanguageDef.GSLTIL.DisplayedRouteValuation
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge
open Mettapedia.GSLT.LanguageDef.GSLTIL.FundedContextualCommit
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteFootprintWaveAdmission
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

universe u

/-! ## Exact wave/commit intersection -/

/-- A selected physical commit drawn from an exact certified route wave.

The evaluation and commit accounts are intentionally different type
parameters.  A runtime may instantiate them with the same carrier, but the
interface supplies no conversion and no authority in either direction. -/
structure CertifiedRouteWaveCommit
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
    {policy : CommitPolicy (RouteCandidate theory Occurrence Answer source)}
    (commitCostAt : Occurrence → CommitAccount)
    (commitSource : CommitAccount)
    (commit : StateCommit algebra effects family policy) where
  selectedInWave : commit.selection.candidate ∈ pair.batch
  funding : FundedStateCommit commitCostAt commitSource commit

namespace CertifiedRouteWaveCommit

variable
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
    {commit : StateCommit algebra effects family policy}

/-- The wave target is the serializable result of evaluating the whole
certified batch.  It remains speculative at this boundary. -/
def speculativeTarget
    (_receipt : CertifiedRouteWaveCommit wave commitCostAt commitSource commit) :
    Network Location Atom :=
  pair.referenceTarget

/-- The physical target is the state exposed by the selected, authorized,
and funded commit receipt. -/
def physicalTarget
    (_receipt : CertifiedRouteWaveCommit wave commitCostAt commitSource commit) :
    Network Location Atom :=
  commit.state

/-- The physical target uses exactly the same candidate transformer that
participated in the certified wave, applied once to the common parent. -/
theorem physicalTarget_is_selected_wave_step
    (receipt : CertifiedRouteWaveCommit wave commitCostAt commitSource commit) :
    receipt.physicalTarget =
      candidateStep algebra effects family.parent
        commit.selection.candidate := by
  calc
    commit.state = algebra.apply family.parent commit.delta :=
      commit.stateExact
    _ = algebra.apply family.parent
        (commit.selection.candidate.delta algebra effects) := by
      rw [commit.deltaExact]
    _ = candidateStep algebra effects family.parent
        commit.selection.candidate := rfl

/-- The selected route's engine demand is computed from its exact retained
physical occurrences, independently of the wave-level account. -/
theorem selected_commit_cost_is_occurrence_grade
    (receipt : CertifiedRouteWaveCommit wave commitCostAt commitSource commit) :
    occurrenceGrade
        (Mettapedia.GSLT.Dynamics.IndexedEventValuation.additive commitCostAt)
        commit.selection.candidate.route =
      some receipt.funding.spent := by
  exact selectedCost_eq_occurrenceGrade commitCostAt commit

/-- The commit receipt exposes exact conservation of its own engine purse. -/
theorem commit_purse_conserved
    (receipt : CertifiedRouteWaveCommit wave commitCostAt commitSource commit) :
    commitSource = receipt.funding.spent + receipt.funding.remaining :=
  receipt.funding.source_eq_spent_add_remaining

/-- Without an exact selected-route purse, even a pre-existing certified wave
cannot be promoted to a physical commit receipt. -/
theorem no_receipt_without_commit_funding
    (insufficient : ¬ Nonempty
      (FundedStateCommit commitCostAt commitSource commit)) :
    ¬ Nonempty
      (CertifiedRouteWaveCommit wave commitCostAt commitSource commit) := by
  rintro ⟨receipt⟩
  exact insufficient ⟨receipt.funding⟩

end CertifiedRouteWaveCommit

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteFootprintWaveAdmission.Canary
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge.Canary

def leftSelection : Selection family.candidates where
  index := 0
  candidate := leftCandidate
  selected := rfl

def leftOnly : CommitPolicy
    (RouteCandidate collisionTheory Nat Bool ()) where
  Allows candidate := candidate.answer = false

def leftAuthorization : AuthorizedSelection leftOnly leftSelection where
  allowed := rfl

def leftCommit : StateCommit networkAlgebra effects family leftOnly :=
  commitState networkAlgebra effects family leftOnly leftSelection
    leftAuthorization

def commitCostAt (_occurrence : Nat) : Nat := 1

def fundedLeft : FundedStateCommit commitCostAt 1 leftCommit where
  funding :=
    { frame := 0
      source_eq := by decide }

def selectedWaveCommit :
    CertifiedRouteWaveCommit certified commitCostAt 1 leftCommit where
  selectedInWave := by
    change leftCandidate ∈ [leftCandidate, rightCandidate]
    simp
  funding := fundedLeft

/-- Positive control: the same receipt supports bulk speculative execution,
then exposes exactly one selected route as the physical state transition and
conserves its separate commit purse. -/
theorem bulk_exploration_then_exact_selected_commit :
    (certified.plan .general).activation = .bulk ∧
      selectedWaveCommit.physicalTarget false = {()} ∧
      selectedWaveCommit.physicalTarget true = ∅ ∧
      selectedWaveCommit.funding.spent = 1 ∧
      selectedWaveCommit.funding.remaining = 0 := by
  constructor
  · exact certified.completeBag_dispatches_bulk rfl
  · decide

/-- Parallel exploration of both compatible deltas is not silently the same
operation as committing the selected left alternative. -/
theorem speculative_wave_target_is_not_selected_physical_target :
    selectedWaveCommit.speculativeTarget ≠
      selectedWaveCommit.physicalTarget := by
  intro same
  have speculativeCard :
      (selectedWaveCommit.speculativeTarget true).card = 1 := by
    exact disjoint_retained_routes_earn_bulk.2.2
  have physicalCard :
      (selectedWaveCommit.physicalTarget true).card = 0 := by
    rw [bulk_exploration_then_exact_selected_commit.2.2.1]
    rfl
  have sameCard :=
    congrArg (fun state : TestState => (state true).card) same
  omega

theorem zero_cannot_fund_selected_commit :
    ¬ Nonempty (FundedStateCommit commitCostAt 0 leftCommit) := by
  rintro ⟨funded⟩
  have equation := funded.funding.source_eq
  change 0 = 1 + funded.funding.frame at equation
  omega

/-- The complete certified wave remains available with its own account, but
that wave license cannot manufacture the independently required commit purse. -/
theorem wave_license_does_not_mint_commit_funding :
    Nonempty
        (CertifiedBatch completeContract
          (IndependentPair.executionSemantics
            (algebra := networkAlgebra) (effects := effects) id)
          family.parent independentPair.referenceTarget Nat unitDemand 2
          independentPair.batch) ∧
      ¬ Nonempty
        (CertifiedRouteWaveCommit
          certified commitCostAt 0 leftCommit) :=
  ⟨⟨certified⟩,
    CertifiedRouteWaveCommit.no_receipt_without_commit_funding
      zero_cannot_fund_selected_commit⟩

def noIntents : IntentPolicy Bool where
  Allows _ := False

/-- A funded state commit still leaves the route's external intent behind a
separate authorization boundary. -/
theorem selected_funded_commit_does_not_authorize_intents :
    Nonempty
        (CertifiedRouteWaveCommit certified commitCostAt 1 leftCommit) ∧
      ¬ Nonempty (AuthorizedIntents noIntents leftCommit) := by
  constructor
  · exact ⟨selectedWaveCommit⟩
  · rintro ⟨authorization⟩
    exact authorization.allowed

end Canary

#print axioms CertifiedRouteWaveCommit.physicalTarget_is_selected_wave_step
#print axioms CertifiedRouteWaveCommit.selected_commit_cost_is_occurrence_grade
#print axioms CertifiedRouteWaveCommit.commit_purse_conserved
#print axioms CertifiedRouteWaveCommit.no_receipt_without_commit_funding
#print axioms Canary.bulk_exploration_then_exact_selected_commit
#print axioms Canary.speculative_wave_target_is_not_selected_physical_target
#print axioms Canary.wave_license_does_not_mint_commit_funding
#print axioms Canary.selected_funded_commit_does_not_authorize_intents

end Mettapedia.GSLT.LanguageDef.GSLTIL.FundedRouteWaveCommit
