import Mettapedia.Logic.PLNProbHOLPlannerBridge

/-!
# ProbHOL Planner Bridge Regression

Regression fixtures for the thin planner-facing bridge from semantic
hierarchical `ProbHOL` through the benchmark LI-style belief shadow into
mixed-mode higher-order guarded planning.

The point of this file is to keep the layering honest:

- `HOL/Probabilistic/*` remains the canonical semantic probability layer,
- `HOL/Probabilistic/BenchmarkBeliefBridge.lean` provides the derived
  benchmark-facing belief shadow,
- `PLNProbHOLPlannerBridge.lean` packages the planner-facing consumption path,
- this file records positive and negative examples for that public bridge.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.HOL.LogicalInduction
open Mettapedia.Logic.HOL.Probabilistic

/-- The concrete leaky planner shadow preserves the canonical benchmark sample. -/
theorem planner_bridge_regression_leaky_sample :
    leakyHigherOrderPlannerShadow.sample = benchmarkBeliefSample := by
  unfold leakyHigherOrderPlannerShadow benchmarkPlannerShadow
  rfl

/-- The carried planner value agrees with the benchmark belief price derived
from semantic `ProbHOL`. -/
theorem planner_bridge_regression_leaky_value :
    leakyHigherOrderPlannerShadow.carried.value =
      some (((benchmarkBeliefPrice PLNMixedModeChainComposition.leakyHigherOrderPayload
        leakyHigherOrderPayload_valid01 : Price01) : Rat)) := by
  unfold leakyHigherOrderPlannerShadow benchmarkPlannerShadow
  simpa using
    higherOrderSemanticContraction_value_eq_benchmarkBeliefPrice
      PLNProofCarryingContractionDemo.softGateStep_C_given_A.query
      PLNMixedModeChainComposition.leakyHigherOrderPayload
      leakyHigherOrderPayload_valid01
      (PLNProofCarryingContractionDemo.softGateStep_C_given_A.sigma ++
        ["explicit latent admissibility regime over the leaky chain fixture"])
      (PLNProofCarryingContractionDemo.softGateStep_C_given_A.provenance ++
        ["finite higher-order regime mixture"])

/-- The planner shadow process tracks the hierarchical benchmark probability on
the intended benchmark sample. -/
theorem planner_bridge_regression_leaky_process_tracks :
    BeliefProcessEventuallyTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkHierarchicalState
        PLNMixedModeChainComposition.leakyHigherOrderPayload
        leakyHigherOrderPayload_valid01)
      leakyHigherOrderPlannerShadow.sample
      leakyHigherOrderPlannerShadow.beliefProcess := by
  unfold leakyHigherOrderPlannerShadow benchmarkPlannerShadow
  simpa using
    benchmarkBeliefProcess_eventuallyTracks_benchmarkHierarchicalProbOn
      PLNMixedModeChainComposition.leakyHigherOrderPayload
      leakyHigherOrderPayload_valid01

/-- The planner shadow is intentionally narrow: it is not a global belief oracle
for the expanded sample containing unrelated formulas. -/
theorem planner_bridge_regression_leaky_day_not_tracks_expanded :
    ¬ BeliefDayTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkHierarchicalState
        PLNMixedModeChainComposition.leakyHigherOrderPayload
        leakyHigherOrderPayload_valid01)
      leakyHigherOrderPlannerShadow.beliefDay
      benchmarkBeliefExpandedSample := by
  simpa [leakyHigherOrderPlannerShadow] using
    benchmarkPlannerShadow_day_not_tracks_expandedSample
      PLNProofCarryingContractionDemo.softGateStep_C_given_A.query
      PLNMixedModeChainComposition.leakyHigherOrderPayload
      leakyHigherOrderPayload_valid01
      (PLNProofCarryingContractionDemo.softGateStep_C_given_A.sigma ++
        ["explicit latent admissibility regime over the leaky chain fixture"])
      (PLNProofCarryingContractionDemo.softGateStep_C_given_A.provenance ++
        ["finite higher-order regime mixture"])

/-- The mixed-mode carried query preserves the semantically justified guard
confidence. -/
theorem planner_bridge_regression_leaky_gate_confidence :
    PLNMixedModeChainComposition.leakyHigherOrderPlan_C.current.gateConfidence =
      some (PLNGuardedHigherOrderSemantics.higherOrderGuardConfidence
        PLNMixedModeChainComposition.leakyHigherOrderPayload) := by
  exact leakyHigherOrderPlan_C_current_gateConfidence_eq_higherOrderGuardConfidence

/-- The mixed-mode carried query still records the originating higher-order
payload explicitly. -/
theorem planner_bridge_regression_leaky_records_payload :
    PLNMixedModeChainComposition.leakyHigherOrderPlan_C.current.higherOrderGuard =
      some PLNMixedModeChainComposition.leakyHigherOrderPayload := by
  exact leakyHigherOrderPlan_C_current_records_payload

end Mettapedia.Logic
