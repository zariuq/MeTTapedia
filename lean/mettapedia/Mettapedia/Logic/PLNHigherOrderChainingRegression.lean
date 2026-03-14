import Mettapedia.Logic.PLNHigherOrderChainingTheorems
import Mettapedia.Logic.PLNRegimeMixtureRegression
import Mettapedia.Logic.PLNProofCarryingContractionDemo
import Mettapedia.Logic.PLNGuardedHigherOrderSemantics
import Mettapedia.Logic.PLNRegimeMixtureTheorems

/-!
# Higher-Order Chaining Regression

Concrete canaries for the abstract higher-order chaining theorem layer.

The point is to show that the generic continuation and reveal-preference
theorems really do land on the existing leaky benchmark fixture, rather than
serving only as abstract packaging.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.PLNMixedModeChainComposition
open Mettapedia.Logic.HOL.Probabilistic

theorem higherOrderChaining_regression_leaky_continue_preserves_semanticStatus :
    leakyHigherOrderPlan_C.current.semanticStatus = .higherOrderSemanticGuarded := by
  simpa [leakyHigherOrderPlan_C, cleanPlan_B, exactStep_B, startPlan]
    using higherOrder_continue_preserves_semanticStatus
      cleanPlan_B
      rfl
      PLNProofCarryingContractionDemo.softGateStep_C_given_A.query
      leakyHigherOrderPayload
      leakyHigherOrderPayload_valid01.validWeights
      (PLNProofCarryingContractionDemo.softGateStep_C_given_A.sigma ++
        ["explicit latent admissibility regime over the leaky chain fixture"])
      (PLNProofCarryingContractionDemo.softGateStep_C_given_A.provenance ++
        ["finite higher-order regime mixture"])
      1

theorem higherOrderChaining_regression_leaky_continue_accumulatedBound_eq :
    leakyHigherOrderPlan_C.accumulatedBound = some (213 / 4420) := by
  have hcombine :=
    higherOrder_continue_accumulatedBound_eq_combineBounds
      cleanPlan_B
      PLNProofCarryingContractionDemo.softGateStep_C_given_A.query
      leakyHigherOrderPayload
      leakyHigherOrderPayload_valid01.validWeights
      (PLNProofCarryingContractionDemo.softGateStep_C_given_A.sigma ++
        ["explicit latent admissibility regime over the leaky chain fixture"])
      (PLNProofCarryingContractionDemo.softGateStep_C_given_A.provenance ++
        ["finite higher-order regime mixture"])
      1
  have hclean :
      cleanPlan_B.accumulatedBound = none := by
    simp [cleanPlan_B, startPlan, exactStep_B,
      PLNGuardedHigherOrderSemantics.liftTheoremExact,
      PLNProbGuardedAdmissibility.ofExactContraction]
  have hradius :
      some (PLNGuardedHigherOrderSemantics.higherOrderSemanticRadius leakyHigherOrderPayload) =
        some (213 / 4420) := by
    simpa [leakyHigherOrder_C, PLNGuardedHigherOrderSemantics.higherOrderSemanticContraction]
      using leakyHigherOrder_C_radius
  change
    (applyStep cleanPlan_B .applyHigherOrderSemantic
      (PLNGuardedHigherOrderSemantics.higherOrderSemanticContraction
        PLNProofCarryingContractionDemo.softGateStep_C_given_A.query
        leakyHigherOrderPayload
        leakyHigherOrderPayload_valid01.validWeights
        (PLNProofCarryingContractionDemo.softGateStep_C_given_A.sigma ++
          ["explicit latent admissibility regime over the leaky chain fixture"])
        (PLNProofCarryingContractionDemo.softGateStep_C_given_A.provenance ++
          ["finite higher-order regime mixture"]))
      ).accumulatedBound = some (213 / 4420)
  rw [hcombine, hclean, hradius]
  simp [combineBounds_none_left]

theorem higherOrderChaining_regression_leaky_continue_value_eq_benchmarkBeliefPrice :
    leakyHigherOrderPlan_C.current.value =
      some (((benchmarkBeliefPrice leakyHigherOrderPayload
        leakyHigherOrderPayload_valid01 : HOL.LogicalInduction.Price01) : Rat)) := by
  simpa [leakyHigherOrderPlan_C, cleanPlan_B, exactStep_B, startPlan]
    using higherOrder_continue_current_value_eq_benchmarkBeliefPrice
      cleanPlan_B
      PLNProofCarryingContractionDemo.softGateStep_C_given_A.query
      leakyHigherOrderPayload
      leakyHigherOrderPayload_valid01
      (PLNProofCarryingContractionDemo.softGateStep_C_given_A.sigma ++
        ["explicit latent admissibility regime over the leaky chain fixture"])
      (PLNProofCarryingContractionDemo.softGateStep_C_given_A.provenance ++
        ["finite higher-order regime mixture"])
      1

theorem higherOrderChaining_regression_leaky_broadQueryError_le_residualMass_mul_branchRadius :
    |(PLNGuardedHigherOrderSemantics.higherOrderSemanticValue leakyHigherOrderPayload : ℝ) -
        benchmarkBranchValuesReal leakyHigherOrderPayload .exactAdmissible| ≤
      (1 - benchmarkWeightsReal leakyHigherOrderPayload .exactAdmissible) *
        PLNRegimeMixtureTheorems.branchRadius
          (benchmarkBranchValuesReal leakyHigherOrderPayload)
          .exactAdmissible := by
  exact higherOrder_continue_broadQueryError_le_residualMass_mul_branchRadius
    leakyHigherOrderPayload
    leakyHigherOrderPayload_valid01

theorem higherOrderChaining_regression_leaky_reveal_preferred_at_zero_cost :
    0 < benchmarkRevealGain leakyHigherOrderPayload 0 := by
  have hvar :
      0 <
        PLNRegimeMixtureTheorems.mixtureVariance
          (benchmarkWeightsReal leakyHigherOrderPayload)
          (benchmarkBranchValuesReal leakyHigherOrderPayload) := by
    rw [regimeMixture_regression_leaky_variance_eq_concrete]
    norm_num
  exact higherOrder_revealPreferred_for_refinedQuery_if_cost_lt_mixtureVariance
    leakyHigherOrderPayload
    0
    hvar

theorem higherOrderChaining_regression_reveal_sets_queryChanged :
    revealThenExactPlan_C.queryChanged = true := by
  simpa [revealThenExactPlan_C, cleanPlan_B, exactStep_C, exactStep_B, startPlan]
    using higherOrder_reveal_sets_queryChanged cleanPlan_B exactStep_C 1

end Mettapedia.Logic
