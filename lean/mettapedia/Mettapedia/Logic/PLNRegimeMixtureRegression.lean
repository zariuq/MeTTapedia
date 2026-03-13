import Mettapedia.Logic.PLNRegimeMixtureBenchmarkBridge
import Mettapedia.Logic.PLNWorldModelRegimeAdmissibilityRegression
import Mettapedia.Logic.PLNProbHOLPlannerBridgeRegression

/-!
# Regime-Mixture Regression

Concrete regression fixtures for the finite regime-mixture theorem family.

This file keeps the Chapter 11 strengthening honest by bundling:

- positive semantic witnesses on the concrete leaky higher-order payload,
- negative reveal-cost witnesses,
- and compatibility with the WM-side regime-sensitive admissibility layer.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.HOL.Probabilistic
open Mettapedia.Logic.PLNGuardedHigherOrderSemantics
open Mettapedia.Logic.PLNMixedModeChainComposition
open Mettapedia.Logic.PLNProbGuardedAdmissibilityDemo
open Mettapedia.Logic.PLNProofCarryingContractionDemo
open Mettapedia.Logic.PLNRegimeMixtureTheorems
open Mettapedia.Logic.PLNWorldModelRegimeAdmissibility
open Mettapedia.Logic.PLNWorldModelRegimeAdmissibilityRegression
open Mettapedia.Hyperseed.Regression

/-- The leaky higher-order fixture instantiates the abstract mixture value to
the same concrete broad-query value already carried by the semantic bridge. -/
theorem regimeMixture_regression_leaky_value_eq_concrete :
    mixtureValue
        (benchmarkWeightsReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload) =
      (133 / 221 : ℝ) := by
  rw [benchmarkMixtureValue_eq_higherOrderSemanticValue]
  norm_num [higherOrderSemanticValue, leakyHigherOrderPayload, leakySemanticWeights,
    leakyRuleEstimate, leakyViolationRadius, softProb_C_true_given_A_true,
    baseProb_A_true, softWeight, baseWeight, bern, pH, pA_given_H, pB_given_H,
    pC_given_A_B_soft, pC_given_B, pD_given_C]

/-- The concrete leaky mixture value stays inside the unit interval. -/
theorem regimeMixture_regression_leaky_value_nonneg :
    0 ≤
      mixtureValue
        (benchmarkWeightsReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload) := by
  rw [regimeMixture_regression_leaky_value_eq_concrete]
  norm_num

/-- The concrete leaky mixture value stays inside the unit interval. -/
theorem regimeMixture_regression_leaky_value_le_one :
    mixtureValue
        (benchmarkWeightsReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload) ≤
      1 := by
  rw [regimeMixture_regression_leaky_value_eq_concrete]
  norm_num

/-- The planner-facing carried value on the leaky fixture still agrees with the
same concrete mixture value. -/
theorem regimeMixture_regression_leaky_planner_value_eq_concrete :
    leakyHigherOrderPlan_C.current.value = some (133 / 221) := by
  rw [leakyHigherOrderPlan_C_current_value_eq_benchmarkBeliefPrice]
  rw [benchmarkBeliefPrice_val]
  norm_num [higherOrderSemanticValue, leakyHigherOrderPayload, leakySemanticWeights,
    leakyRuleEstimate, leakyViolationRadius, softProb_C_true_given_A_true,
    baseProb_A_true, softWeight, baseWeight, bern, pH, pA_given_H, pB_given_H,
    pC_given_A_B_soft, pC_given_B, pD_given_C]

/-- On the leaky fixture, the finite-mixture predictor weakly dominates direct
exact continuation under squared loss. -/
theorem regimeMixture_regression_leaky_mixtureVariance_le_exactBranchRisk :
    mixtureVariance
        (benchmarkWeightsReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload) ≤
      expectedSquaredLoss
        (benchmarkWeightsReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload .exactAdmissible) := by
  exact leaky_regimeMixture_mixtureSquaredLoss_le_exactBranchRisk

/-- The concrete leaky latent-regime variance is nonzero and computable. -/
theorem regimeMixture_regression_leaky_variance_eq_concrete :
    mixtureVariance
        (benchmarkWeightsReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload) =
      (9663597 / 86350888000 : ℝ) := by
  unfold mixtureVariance expectedSquaredLoss mixtureValue
  have huniv :
      (Finset.univ : Finset GuardRegime) =
        { .exactAdmissible, .boundedViolation, .fallbackRequired } := by
    ext g
    cases g <;> simp
  rw [huniv]
  simp
  norm_num [benchmarkWeightsReal, benchmarkBranchValuesReal, leakyHigherOrderPayload,
    leakySemanticWeights, leakyRuleEstimate, leakyViolationRadius,
    softProb_C_true_given_A_true, baseProb_A_true, softWeight, baseWeight, bern, pH,
    pA_given_H, pB_given_H, pC_given_A_B_soft, pC_given_B, pD_given_C]

/-- Zero reveal cost is enough to make reveal strictly preferable on the leaky
fixture, because the latent-regime variance is genuinely positive. -/
theorem regimeMixture_regression_leaky_reveal_preferred_at_zero_cost :
    0 < benchmarkRevealGain leakyHigherOrderPayload 0 := by
  rw [benchmarkRevealGain_eq_variance_minus_cost]
  rw [regimeMixture_regression_leaky_variance_eq_concrete]
  norm_num

/-- Unit reveal cost is too expensive on the leaky fixture, so reveal is not
preferred at that cost level. -/
theorem regimeMixture_regression_leaky_reveal_not_preferred_at_cost_one :
    benchmarkRevealGain leakyHigherOrderPayload 1 ≤ 0 := by
  rw [benchmarkRevealGain_eq_variance_minus_cost]
  rw [regimeMixture_regression_leaky_variance_eq_concrete]
  norm_num

/-- The WM-side regime-sensitive admissibility witness remains available as the
admissibility-side counterpart to the regime-mixture theorems. -/
theorem regimeMixture_regression_sameWM_differentRegimes_differentAdmissibleDiscoveries
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∉
        wmAdmissibleRegionAt
          (State := Multiset AgentObservation) (Query := AgentQuery)
          groundedStatefulQueryPerspective σ 3 Set.univ 1 ∧
      AgentQuery.awareReady ∈
        wmAdmissibleRegionAt
          (State := Multiset AgentObservation) (Query := AgentQuery)
          regimeSensitiveQueryPerspective σ 3 Set.univ 1 := by
  exact sameWM_differentRegimes_differentAdmissibleDiscoveries hσ

/-- Chapter-11-facing compatibility package: the concrete higher-order leaky
mixture theorem and the WM-side regime-sensitive admissibility witness can be
quoted together without changing either layer's semantics. -/
theorem regimeMixture_regression_chapter11_semantic_and_wm_split
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    mixtureVariance
        (benchmarkWeightsReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload) ≤
      expectedSquaredLoss
        (benchmarkWeightsReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload .exactAdmissible) ∧
      AgentQuery.awareReady ∉
        wmAdmissibleRegionAt
          (State := Multiset AgentObservation) (Query := AgentQuery)
          groundedStatefulQueryPerspective σ 3 Set.univ 1 ∧
      AgentQuery.awareReady ∈
        wmAdmissibleRegionAt
          (State := Multiset AgentObservation) (Query := AgentQuery)
          regimeSensitiveQueryPerspective σ 3 Set.univ 1 := by
  exact ⟨regimeMixture_regression_leaky_mixtureVariance_le_exactBranchRisk,
    (regimeMixture_regression_sameWM_differentRegimes_differentAdmissibleDiscoveries hσ).1,
    (regimeMixture_regression_sameWM_differentRegimes_differentAdmissibleDiscoveries hσ).2⟩

end Mettapedia.Logic
