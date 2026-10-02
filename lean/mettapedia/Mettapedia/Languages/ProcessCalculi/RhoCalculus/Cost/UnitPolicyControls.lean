import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.UnitPolicy
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Path
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationVerticalBraid

/-!
# Authored communication and executable unit-policy controls

The existing typed rho communication reduces in the unmetered language.
Its wrapped counterpart cannot fire without funding, while its positive
funded counterpart fires by the existing `CostStep` rule.  Raw runtime
controls distinguish absent funding, an empty purse, an unsupported unit-key
cell, and an actual matching positive head.

Occurrence-bearing paths additionally show that a firing count and a
consumed-cell count differ under split funding.  Both paths below perform one
communication and spend the same signature multiset; one consumes one head
and the other consumes two.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.UnitPolicyControls

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DependentReflectiveCommunicationCell
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationVerticalBraid

/-- The actual authored COMM reduces, while its unfunded wrapper is blocked. -/
theorem authored_comm_unfunded_wrapper_blocked :
    rhoLanguageDefGSLT.Step
        (exactEndpoints zeroCommunication).1
        (exactEndpoints zeroCommunication).2 ∧
      ∀ location spend target,
        ¬ CostStep {communicationCostRedex} location spend target := by
  refine ⟨typedCommunication_vertical_braid.exactRhoStep, ?_⟩
  intro location spend target
  exact CostStep.signed_singleton_blocked _ _ location spend target

/-- Supplying the actual positive purse enables that same COMM counterpart. -/
theorem authored_comm_funded_wrapper_fires :
    CostStep communicationCostSource communicationCostChannel
      communicationSeal communicationCostTarget := by
  exact communicationCostStep

/-- An encoding with an empty-purse unit at this running source cannot
preserve the authored transitions in the existing positive meter. -/
theorem no_transition_preserving_empty_purse_embedding
    (encode : RhoProcess → CostConfig CommunicationFundingAtom)
    (signature : CostSig CommunicationFundingAtom)
    (emptyUnitAtRedex :
      encode (exactEndpoints zeroCommunication).1 =
        {CostTerm.signed
          (.par (.recv communicationCostChannel .nil)
            (.send communicationCostChannel .nil)) signature} +
        {CostTerm.purse communicationCostChannel .empty}) :
    ¬ (∀ source target, rhoLanguageDefGSLT.Step source target →
      ∃ location spend,
        CostStep (encode source) location spend (encode target)) := by
  intro preserves
  obtain ⟨location, spend, step⟩ :=
    preserves _ _ typedCommunication_vertical_braid.exactRhoStep
  rw [emptyUnitAtRedex] at step
  exact CostStep.signed_with_empty_purse_blocked _ signature
    communicationCostChannel location spend _ step

/-- Pricing the authentic seal at zero does not make its unfunded redex run. -/
theorem authored_comm_zero_price_unfunded_blocked :
    CostSig.additiveFold
        (fun _ : CommunicationFundingAtom => (0 : Nat)) communicationSeal = 0 ∧
      ∀ target,
        ¬ CostStep {communicationCostRedex} communicationCostChannel
          communicationSeal target := by
  constructor
  · simp [communicationSeal]
  · intro target
    exact CostStep.signed_singleton_blocked _ _ _ _ target

/-- A zero-spend transition is absent even from the positively funded source. -/
theorem authored_comm_has_no_unit_spend :
    ¬ CostStep communicationCostSource communicationCostChannel
      0 communicationCostTarget :=
  CostStep.no_unit_spend _ _ _

def rawChannel : RawCostName := .signature ["c"]

def rawWhole (signature : RawCostSig) : RawCostTerm :=
  .signed (.par (.recv rawChannel .nil) (.send rawChannel .nil)) signature

def unfunded : RawCostTerm := rawWhole ["a"]

def emptyPurse : RawCostTerm :=
  .par unfunded (.purse rawChannel [])

def unitKeyPurse : RawCostTerm :=
  .par unfunded (.purse rawChannel [[]])

def singleHead : RawCostTerm :=
  .par unfunded (.purse rawChannel [["a"]])

def wrongLocation : RawCostTerm :=
  .par unfunded (.purse (.signature ["other"]) [["a"]])

def wrongKey : RawCostTerm :=
  .par unfunded (.purse rawChannel [["b"]])

def unitKeyWrapper : RawCostTerm := rawWhole []

/-- The unfunded redex is accepted syntax and has no executable firing. -/
theorem unfunded_runtime_blocked :
    unfunded.supported = true ∧ runtimeCostFrontier unfunded = some [] := by
  decide

/-- A depleted purse is observable accepted syntax and supplies no head. -/
theorem empty_purse_runtime_blocked :
    emptyPurse.supported = true ∧ runtimeCostFrontier emptyPurse = some [] := by
  decide

/-- A literal unit-key cell is rejected by the positive runtime fragment. -/
theorem unit_key_purse_runtime_unsupported :
    unitKeyPurse.supported = false ∧ runtimeCostFrontier unitKeyPurse = none := by
  decide

/-- A literal unit-key wrapper is likewise outside that public fragment. -/
theorem unit_key_wrapper_runtime_unsupported :
    unitKeyWrapper.supported = false ∧ runtimeCostFrontier unitKeyWrapper = none := by
  decide

/-- A matching positive head produces one actual runtime transition. -/
theorem single_head_runtime_fires :
    singleHead.supported = true ∧
      (runtimeCostFrontier singleHead).map List.length = some 1 := by
  decide

/-- The right key at the wrong location supplies no authority. -/
theorem wrong_location_runtime_blocked :
    wrongLocation.supported = true ∧
      runtimeCostFrontier wrongLocation = some [] := by
  decide

/-- A different positive key at the right location supplies no cover. -/
theorem wrong_key_runtime_blocked :
    wrongKey.supported = true ∧ runtimeCostFrontier wrongKey = some [] := by
  decide

def combinedHead : RawCostTerm :=
  .par (rawWhole ["a", "b"]) (.purse rawChannel [["a", "b"]])

def splitHeads : RawCostTerm :=
  .par (rawWhole ["a", "b"])
    (.par (.purse rawChannel [["a"]]) (.purse rawChannel [["b"]]))

/-- Build an actual one-firing path from an enabled occurrence. -/
def fireOnce (term : RawCostTerm) (supported : term.wellFormed = true)
    (step : RawRuntimeStep)
    (enabled : step ∈ runtimeCostCandidatesFromConfig term.normalizeConfig) :
    CostPath 0 (initialTraceComponents term) 1
      (applyTracedStep (initialTraceComponents term) step 0) := by
  have initiallySupported := initialTraceComponents_wellFormed supported
  have initiallyBounded := initialTraceComponents_before term
  have occurrence : step ∈ runtimeCostCandidatesFromConfig
      ((initialTraceComponents term).map RawTraceComponent.term) := by
    simpa [initialTraceComponents, List.map_map, Function.comp_def] using enabled
  exact .fire initiallySupported initiallyBounded step occurrence
    (.done (applyTracedStep_wellFormed initiallySupported occurrence 0)
      (applyTracedStep_before initiallyBounded step))

def combinedHeadStep : RawRuntimeStep :=
  (runtimeCostCandidatesFromConfig combinedHead.normalizeConfig)[0]'(by decide)

def splitHeadsStep : RawRuntimeStep :=
  (runtimeCostCandidatesFromConfig splitHeads.normalizeConfig)[0]'(by decide)

def combinedHeadPath :
    CostPath 0 (initialTraceComponents combinedHead) 1
      (applyTracedStep (initialTraceComponents combinedHead) combinedHeadStep 0) :=
  fireOnce combinedHead (by decide) combinedHeadStep (by decide)

def splitHeadsPath :
    CostPath 0 (initialTraceComponents splitHeads) 1
      (applyTracedStep (initialTraceComponents splitHeads) splitHeadsStep 0) :=
  fireOnce splitHeads (by decide) splitHeadsStep (by decide)

/-- One funded COMM with one selected head consumes exactly one cell. -/
theorem combined_head_path_counts :
    combinedHeadPath.depth = 1 ∧ combinedHeadPath.consumedPurseCells = 1 := by
  decide

/-- One funded COMM with two selected heads consumes two cells. -/
theorem split_heads_path_counts :
    splitHeadsPath.depth = 1 ∧ splitHeadsPath.consumedPurseCells = 2 := by
  decide

/-- Split funding refutes an unconditional cells-equal-firings equation. -/
theorem split_heads_cells_ne_firings :
    splitHeadsPath.consumedPurseCells ≠ splitHeadsPath.depth := by
  rw [split_heads_path_counts.1, split_heads_path_counts.2]
  decide

/-- Both actual paths emit one event with the same aggregate raw signature. -/
theorem same_spend_different_cell_counts :
    combinedHeadPath.rawEmission.map RawEmittedEvent.rawSpend = [["a", "b"]] ∧
      splitHeadsPath.rawEmission.map RawEmittedEvent.rawSpend = [["a", "b"]] ∧
      combinedHeadPath.rawEmission.map (fun event => event.funding.length) = [1] ∧
      splitHeadsPath.rawEmission.map (fun event => event.funding.length) = [2] := by
  decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.UnitPolicyControls
