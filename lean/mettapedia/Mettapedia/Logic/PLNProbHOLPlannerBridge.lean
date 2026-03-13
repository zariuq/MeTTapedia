import Mettapedia.Logic.PLNMixedModeChainComposition
import Mettapedia.Logic.HOL.Probabilistic.BenchmarkBeliefBridge

/-!
# PLN ProbHOL Planner Bridge

This module gives the planner/control layer a thin way to consume the semantic
`ProbHOL` benchmark bridge without letting planner-facing scores become the
canonical semantics.

The intended layering is:

- `HOL/Probabilistic/BenchmarkBridge.lean`: semantic hierarchical benchmark state
- `HOL/Probabilistic/BenchmarkBeliefBridge.lean`: derived LI-style belief view
- this file: planner-facing packaging of the carried query together with that
  belief shadow

This follows the higher-order probability and logical-induction discipline
already adopted in the repository:

- Henry E. Kyburg, *Higher Order Probabilities*
- Haim Gaifman, *A Theory of Higher Order Probabilities* (1986)
- Scott Garrabrant, Tsvi Benson-Tilsen, Andrew Critch, Nate Soares, and
  Jessica Taylor, *Logical Induction*, arXiv:1609.03543v5 (2020)
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.PLNGuardedHigherOrderSemantics
open Mettapedia.Logic.PLNMixedModeChainComposition
open Mettapedia.Logic.PLNProbGuardedAdmissibilityDemo
open Mettapedia.Logic.PLNProofCarryingContractionDemo
open Mettapedia.Logic.HOL.LogicalInduction
open Mettapedia.Logic.HOL.Probabilistic

/-- Planner-facing shadow of one semantically justified higher-order guarded
step.  The carried query remains the planner object, while the belief day and
belief process expose the theorem-backed semantic shadow. -/
structure BenchmarkPlannerShadow where
  carried : SemanticProbGuardedQuery
  beliefDay : BeliefDay BenchmarkConst
  beliefProcess : BeliefProcess BenchmarkConst
  sample : Finset (ClosedFormulaCode BenchmarkConst)

/-- Canonical planner-facing shadow induced by a valid benchmark payload. -/
noncomputable def benchmarkPlannerShadow
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) : BenchmarkPlannerShadow where
  carried := higherOrderSemanticContraction query payload hvalid.validWeights sigma provenance
  beliefDay := benchmarkBeliefDay payload hvalid
  beliefProcess := benchmarkBeliefProcess payload hvalid
  sample := benchmarkBeliefSample

@[simp] theorem benchmarkPlannerShadow_sample
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    (benchmarkPlannerShadow query payload hvalid sigma provenance).sample =
      benchmarkBeliefSample := by
  rfl

theorem benchmarkPlannerShadow_carried_value_eq_benchmarkBeliefPrice
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    (benchmarkPlannerShadow query payload hvalid sigma provenance).carried.value =
      some (((benchmarkBeliefPrice payload hvalid : Price01) : Rat)) := by
  simpa [benchmarkPlannerShadow] using
    higherOrderSemanticContraction_value_eq_benchmarkBeliefPrice
      query payload hvalid sigma provenance

theorem benchmarkPlannerShadow_carried_status
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    (benchmarkPlannerShadow query payload hvalid sigma provenance).carried.semanticStatus =
      .higherOrderSemanticGuarded := by
  rfl

theorem benchmarkPlannerShadow_carried_gateConfidence
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    (benchmarkPlannerShadow query payload hvalid sigma provenance).carried.gateConfidence =
      some (higherOrderGuardConfidence payload) := by
  rfl

theorem benchmarkPlannerShadow_carried_violationBound
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    (benchmarkPlannerShadow query payload hvalid sigma provenance).carried.violationBound =
      some (higherOrderSemanticRadius payload) := by
  rfl

theorem benchmarkPlannerShadow_carried_records_payload
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    (benchmarkPlannerShadow query payload hvalid sigma provenance).carried.higherOrderGuard =
      some payload := by
  rfl

theorem benchmarkPlannerShadow_day_tracks_hierarchicalProbOn
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    BeliefDayTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkHierarchicalState payload hvalid)
      (benchmarkPlannerShadow query payload hvalid sigma provenance).beliefDay
      (benchmarkPlannerShadow query payload hvalid sigma provenance).sample := by
  simpa [benchmarkPlannerShadow] using
    benchmarkBeliefDay_tracks_benchmarkHierarchicalProbOn payload hvalid

theorem benchmarkPlannerShadow_process_tracks_hierarchicalProbOn
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    BeliefProcessEventuallyTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkHierarchicalState payload hvalid)
      (benchmarkPlannerShadow query payload hvalid sigma provenance).sample
      (benchmarkPlannerShadow query payload hvalid sigma provenance).beliefProcess := by
  simpa [benchmarkPlannerShadow] using
    benchmarkBeliefProcess_eventuallyTracks_benchmarkHierarchicalProbOn payload hvalid

/-- The planner-facing benchmark shadow also factors through the richer latent
benchmark hierarchy for any explicit latent profile, because the current
benchmark belief adapter is already tracking the canonical semantic-vs-belief
bridge there. -/
theorem benchmarkPlannerShadow_day_tracks_benchmarkLatentHierarchicalProbOn
    (profile : BenchmarkLatentProfile)
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    BeliefDayTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkLatentHierarchicalState profile payload hvalid)
      (benchmarkPlannerShadow query payload hvalid sigma provenance).beliefDay
      (benchmarkPlannerShadow query payload hvalid sigma provenance).sample := by
  simpa [benchmarkPlannerShadow] using
    benchmarkBeliefDay_tracks_benchmarkLatentHierarchicalProbOn profile payload hvalid

/-- Process-level variant of the preceding latent benchmark tracking theorem. -/
theorem benchmarkPlannerShadow_process_tracks_benchmarkLatentHierarchicalProbOn
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
  simpa [benchmarkPlannerShadow] using
    benchmarkBeliefProcess_eventuallyTracks_benchmarkLatentHierarchicalProbOn profile payload hvalid

theorem benchmarkPlannerShadow_day_not_tracks_expandedSample
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    ¬ BeliefDayTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkHierarchicalState payload hvalid)
      (benchmarkPlannerShadow query payload hvalid sigma provenance).beliefDay
      benchmarkBeliefExpandedSample := by
  simpa [benchmarkPlannerShadow] using
    benchmarkBeliefDay_not_tracks_benchmarkHierarchicalProbOn_with_top payload hvalid

/-- Negative latent-profile canary: even after making context/trust/topology
explicit, the planner shadow remains query-focused rather than becoming a
global oracle for unrelated formulas. -/
theorem benchmarkPlannerShadow_day_not_tracks_benchmarkLatentExpandedSample
    (profile : BenchmarkLatentProfile)
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    ¬ BeliefDayTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkLatentHierarchicalState profile payload hvalid)
      (benchmarkPlannerShadow query payload hvalid sigma provenance).beliefDay
      benchmarkBeliefExpandedSample := by
  simpa [benchmarkPlannerShadow] using
    benchmarkBeliefDay_not_tracks_benchmarkLatentHierarchicalProbOn_with_top
      profile payload hvalid

/-- The concrete leaky higher-order payload already used by the mixed-mode
planning demo is a valid benchmark payload in `[0,1]`. -/
theorem leakyHigherOrderPayload_valid01 :
    ValidBenchmarkPayload01 leakyHigherOrderPayload := by
  refine ⟨leakySemanticWeights_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [leakyHigherOrderPayload, leakyRuleEstimate]
  · norm_num [leakyHigherOrderPayload, leakyRuleEstimate]
  · norm_num [leakyHigherOrderPayload, leakyRuleEstimate, leakyViolationRadius]
  · norm_num [leakyHigherOrderPayload, leakyRuleEstimate, leakyViolationRadius]
  · norm_num [leakyHigherOrderPayload, softProb_C_true_given_A_true_value]
  · norm_num [leakyHigherOrderPayload, softProb_C_true_given_A_true_value]

/-- Planner-facing shadow for the concrete leaky higher-order fixture. -/
noncomputable def leakyHigherOrderPlannerShadow : BenchmarkPlannerShadow :=
  benchmarkPlannerShadow
    softGateStep_C_given_A.query
    leakyHigherOrderPayload
    leakyHigherOrderPayload_valid01
    (softGateStep_C_given_A.sigma ++
      ["explicit latent admissibility regime over the leaky chain fixture"])
    (softGateStep_C_given_A.provenance ++
      ["finite higher-order regime mixture"])

theorem leakyHigherOrderPlannerShadow_carried_value_eq_benchmarkBeliefPrice :
    leakyHigherOrderPlannerShadow.carried.value =
      some (((benchmarkBeliefPrice leakyHigherOrderPayload
        leakyHigherOrderPayload_valid01 : Price01) : Rat)) := by
  unfold leakyHigherOrderPlannerShadow benchmarkPlannerShadow
  simpa using
    higherOrderSemanticContraction_value_eq_benchmarkBeliefPrice
      softGateStep_C_given_A.query
      leakyHigherOrderPayload
      leakyHigherOrderPayload_valid01
      (softGateStep_C_given_A.sigma ++
        ["explicit latent admissibility regime over the leaky chain fixture"])
      (softGateStep_C_given_A.provenance ++
        ["finite higher-order regime mixture"])

theorem leakyHigherOrderPlannerShadow_process_tracks_hierarchicalProbOn :
    BeliefProcessEventuallyTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkHierarchicalState leakyHigherOrderPayload leakyHigherOrderPayload_valid01)
      leakyHigherOrderPlannerShadow.sample
      leakyHigherOrderPlannerShadow.beliefProcess := by
  unfold leakyHigherOrderPlannerShadow benchmarkPlannerShadow
  simpa using
    benchmarkBeliefProcess_eventuallyTracks_benchmarkHierarchicalProbOn
      leakyHigherOrderPayload
      leakyHigherOrderPayload_valid01

/-- The concrete leaky planner shadow also tracks the richer default latent
benchmark hierarchy on its intended sample. -/
theorem leakyHigherOrderPlannerShadow_process_tracks_defaultBenchmarkLatentHierarchicalProbOn :
    BeliefProcessEventuallyTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkLatentHierarchicalState
        defaultBenchmarkLatentProfile
        leakyHigherOrderPayload
        leakyHigherOrderPayload_valid01)
      leakyHigherOrderPlannerShadow.sample
      leakyHigherOrderPlannerShadow.beliefProcess := by
  unfold leakyHigherOrderPlannerShadow benchmarkPlannerShadow
  simpa using
    benchmarkBeliefProcess_eventuallyTracks_benchmarkLatentHierarchicalProbOn
      defaultBenchmarkLatentProfile
      leakyHigherOrderPayload
      leakyHigherOrderPayload_valid01

/-- The existing mixed-mode higher-order leaky plan can therefore be consumed by
the planner as the benchmark belief price extracted from semantic `ProbHOL`. -/
theorem leakyHigherOrderPlan_C_current_value_eq_benchmarkBeliefPrice :
    leakyHigherOrderPlan_C.current.value =
      some (((benchmarkBeliefPrice leakyHigherOrderPayload
        leakyHigherOrderPayload_valid01 : Price01) : Rat)) := by
  rw [PLNMixedModeChainComposition.leakyHigherOrderPlan_C_value]
  congr 1
  rw [benchmarkBeliefPrice_val]
  norm_num [higherOrderSemanticValue, leakyHigherOrderPayload, leakySemanticWeights,
    leakyRuleEstimate, leakyViolationRadius, softProb_C_true_given_A_true,
    baseProb_A_true, softWeight, baseWeight, bern, pH, pA_given_H, pB_given_H,
    pC_given_A_B_soft, pC_given_B, pD_given_C]

theorem leakyHigherOrderPlan_C_current_gateConfidence_eq_higherOrderGuardConfidence :
    leakyHigherOrderPlan_C.current.gateConfidence =
      some (higherOrderGuardConfidence leakyHigherOrderPayload) := by
  rfl

theorem leakyHigherOrderPlan_C_current_records_payload :
    leakyHigherOrderPlan_C.current.higherOrderGuard = some leakyHigherOrderPayload := by
  rfl

end Mettapedia.Logic
