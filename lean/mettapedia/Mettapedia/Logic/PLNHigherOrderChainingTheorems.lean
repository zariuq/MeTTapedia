import Mettapedia.Logic.PLNRegimeMixtureBenchmarkBridge
import Mettapedia.Logic.PLNProbHOLPlannerBridge

/-!
# Higher-Order Chaining Theorems

This module lifts the existing higher-order guarded, regime-mixture, and
semantic-to-belief bridge layers into theorem families about guarded
continuation itself.

The point is not to formalize the current benchmark heuristics.  The point is to
prove that:

- explicit 2nd-order regime payloads can license continued guarded chaining,
- reveal preferences can be stated by a clean variance/cost criterion,
- 3rd-order latent coordinates remain theorem-visible through the semantic
  hierarchy and planner shadow,
- and the whole story still flattens to the carried first-order decision object.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.PLNGuardedHigherOrderSemantics
open Mettapedia.Logic.PLNMixedModeChainComposition
open Mettapedia.Logic.PLNRegimeMixtureTheorems
open Mettapedia.Logic.HOL.LogicalInduction
open Mettapedia.Logic.HOL.Probabilistic

/-- Continuing from an exact theorem-backed state with a higher-order semantic
step upgrades the carried plan to higher-order semantic guardedness. -/
theorem higherOrder_continue_preserves_semanticStatus
    (prev : MixedModePlan)
    (hprev : prev.current.semanticStatus = .theoremCertifiedExact)
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hweights : ValidGuardRegimeWeights payload.weights)
    (sigma provenance : List String)
    (stepCost : Nat := 1) :
    (applyStep prev .applyHigherOrderSemantic
      (higherOrderSemanticContraction query payload hweights sigma provenance)
      stepCost).current.semanticStatus = .higherOrderSemanticGuarded := by
  simp [applyStep, hprev, composeSemanticStatus, higherOrderSemanticContraction]

/-- Higher-order continuation accumulates exactly the conservative combined
radius of the previous plan and the higher-order semantic step. -/
theorem higherOrder_continue_accumulatedBound_eq_combineBounds
    (prev : MixedModePlan)
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hweights : ValidGuardRegimeWeights payload.weights)
    (sigma provenance : List String)
    (stepCost : Nat := 1) :
    (applyStep prev .applyHigherOrderSemantic
      (higherOrderSemanticContraction query payload hweights sigma provenance)
      stepCost).accumulatedBound =
      combineBounds prev.accumulatedBound (some (higherOrderSemanticRadius payload)) := by
  simp [applyStep, higherOrderSemanticContraction]

/-- A non-reveal higher-order continuation does not change the question being
answered. -/
theorem higherOrder_continue_keeps_query_when_not_reveal
    (prev : MixedModePlan)
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hweights : ValidGuardRegimeWeights payload.weights)
    (sigma provenance : List String)
    (stepCost : Nat := 1) :
    (applyStep prev .applyHigherOrderSemantic
      (higherOrderSemanticContraction query payload hweights sigma provenance)
      stepCost).queryChanged = prev.queryChanged := by
  simp [applyStep, actionChangesQuery, higherOrderSemanticContraction]

/-- Reveal explicitly changes the query being answered. -/
theorem higherOrder_reveal_sets_queryChanged
    (prev : MixedModePlan)
    (next : SemanticProbGuardedQuery)
    (stepCost : Nat := 1) :
    (applyStep prev .revealContext next stepCost).queryChanged = true := by
  simp [applyStep, actionChangesQuery]

/-- The current carried value after higher-order continuation is exactly the
flattened higher-order semantic value. -/
theorem higherOrder_continue_current_value_eq_higherOrderSemanticValue
    (prev : MixedModePlan)
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hweights : ValidGuardRegimeWeights payload.weights)
    (sigma provenance : List String)
    (stepCost : Nat := 1) :
    (applyStep prev .applyHigherOrderSemantic
      (higherOrderSemanticContraction query payload hweights sigma provenance)
      stepCost).current.value = some (higherOrderSemanticValue payload) := by
  simp [applyStep, higherOrderSemanticContraction]

/-- Higher-order continuation records the expected higher-order guard
confidence. -/
theorem higherOrder_continue_current_gateConfidence_eq_higherOrderGuardConfidence
    (prev : MixedModePlan)
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hweights : ValidGuardRegimeWeights payload.weights)
    (sigma provenance : List String)
    (stepCost : Nat := 1) :
    (applyStep prev .applyHigherOrderSemantic
      (higherOrderSemanticContraction query payload hweights sigma provenance)
      stepCost).current.gateConfidence = some (higherOrderGuardConfidence payload) := by
  simp [applyStep, higherOrderSemanticContraction]

/-- Higher-order continuation carries the explicit higher-order payload, rather
than collapsing it into a bare controller score. -/
theorem higherOrder_continue_current_records_payload
    (prev : MixedModePlan)
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hweights : ValidGuardRegimeWeights payload.weights)
    (sigma provenance : List String)
    (stepCost : Nat := 1) :
    (applyStep prev .applyHigherOrderSemantic
      (higherOrderSemanticContraction query payload hweights sigma provenance)
      stepCost).current.higherOrderGuard = some payload := by
  simp [applyStep, higherOrderSemanticContraction]

/-- In the benchmark bridge, the carried value after higher-order continuation
agrees with the semantic benchmark belief price. -/
theorem higherOrder_continue_current_value_eq_benchmarkBeliefPrice
    (prev : MixedModePlan)
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String)
    (stepCost : Nat := 1) :
    (applyStep prev .applyHigherOrderSemantic
      (higherOrderSemanticContraction query payload hvalid.validWeights sigma provenance)
      stepCost).current.value =
      some (((benchmarkBeliefPrice payload hvalid : Price01) : Rat)) := by
  simp [applyStep, higherOrderSemanticContraction, benchmarkBeliefPrice_val]

/-- The carried value after higher-order continuation agrees with the value seen
by the planner-facing semantic shadow. -/
theorem higherOrder_continue_current_value_eq_plannerShadow_carried_value
    (prev : MixedModePlan)
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String)
    (stepCost : Nat := 1) :
      (applyStep prev .applyHigherOrderSemantic
      (higherOrderSemanticContraction query payload hvalid.validWeights sigma provenance)
      stepCost).current.value =
      (benchmarkPlannerShadow query payload hvalid sigma provenance).carried.value := by
  simp [applyStep, benchmarkPlannerShadow, higherOrderSemanticContraction]

/-- The planner-facing shadow induced by a higher-order payload still tracks the
latent hierarchical benchmark probability for any explicit latent profile. -/
theorem higherOrder_continue_plannerShadow_process_tracks_benchmarkLatentHierarchicalProbOn
    (profile : BenchmarkLatentProfile)
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    BeliefProcessEventuallyTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkLatentHierarchicalState profile payload hvalid)
      (benchmarkPlannerShadow query payload hvalid sigma provenance).sample
      (benchmarkPlannerShadow query payload hvalid sigma provenance).beliefProcess := by
  exact
    benchmarkPlannerShadow_process_tracks_benchmarkLatentHierarchicalProbOn
      profile query payload hvalid sigma provenance

/-- Broad-query continuation error is controlled by the existing
residual-mass-times-branch-radius bound. -/
theorem higherOrder_continue_broadQueryError_le_residualMass_mul_branchRadius
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    |(higherOrderSemanticValue payload : ℝ) -
        benchmarkBranchValuesReal payload .exactAdmissible| ≤
      (1 - benchmarkWeightsReal payload .exactAdmissible) *
        branchRadius (benchmarkBranchValuesReal payload) .exactAdmissible := by
  rw [← benchmarkMixtureValue_eq_higherOrderSemanticValue]
  exact benchmarkDirectApprox_exactBranch_bound payload hvalid

/-- The higher-order mixture predictor weakly dominates direct exact-branch
continuation under squared loss. -/
theorem higherOrder_continue_mixtureSquaredLoss_le_exactBranchRisk
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    mixtureVariance (benchmarkWeightsReal payload) (benchmarkBranchValuesReal payload) ≤
      expectedSquaredLoss
        (benchmarkWeightsReal payload)
        (benchmarkBranchValuesReal payload)
        (benchmarkBranchValuesReal payload .exactAdmissible) := by
  exact benchmarkMixtureSquaredLoss_le_exactBranchRisk payload hvalid

/-- Reveal is justified for the refined query whenever reveal cost is below the
mixture variance. -/
theorem higherOrder_revealPreferred_for_refinedQuery_if_cost_lt_mixtureVariance
    (payload : HigherOrderGuardPayload)
    (c : ℝ)
    (hc : c <
      mixtureVariance (benchmarkWeightsReal payload) (benchmarkBranchValuesReal payload)) :
    0 < benchmarkRevealGain payload c := by
  exact benchmarkRevealPreferred_if_cost_lt_variance payload c hc

/-- Decision-time flattening is sound: the abstract finite-regime mixture, the
semantic higher-order value, and the planner-facing carried value all agree on
the first-order quantity consumed by action selection. -/
theorem higherOrder_decision_flattening_sound
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    :
    mixtureValue (benchmarkWeightsReal payload) (benchmarkBranchValuesReal payload) =
        (higherOrderSemanticValue payload : ℝ) ∧
      (((benchmarkBeliefPrice payload hvalid : Price01) : Rat)) =
        higherOrderSemanticValue payload := by
  constructor
  · exact benchmarkMixtureValue_eq_higherOrderSemanticValue payload
  · rw [benchmarkBeliefPrice_val]

end Mettapedia.Logic
