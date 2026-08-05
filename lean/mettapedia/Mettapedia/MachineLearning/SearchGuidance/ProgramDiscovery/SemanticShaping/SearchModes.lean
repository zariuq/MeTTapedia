import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping.RepairEvidence
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.BipartitePortfolio

/-!
# Target-guided, corpus-wide, and hybrid search

Completed checker-backed outputs are finite program-target relations.  The
extensional hybrid view is their union and therefore preserves each arm's
coverage.  This statement must not be confused with a finite-budget allocation
claim: splitting a fixed budget can be strictly worse than the best single
arm.  Complementarity, not standalone yield alone, determines portfolio value.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping

open Mettapedia.MachineLearning.SearchGuidance
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

universe uP uT

/-- Two exact checker-backed search outputs. -/
structure SearchModeOutputs (Program : Type uP) (Target : Type uT) where
  targetGuided : SolveRelation Program Target
  corpusWide : SolveRelation Program Target

namespace SearchModeOutputs

variable {Program : Type uP} {Target : Type uT}
variable [DecidableEq Program] [DecidableEq Target]

/-- Hybrid accounting is exact set union after both searches have completed. -/
def hybrid (outputs : SearchModeOutputs Program Target) :
    SolveRelation Program Target :=
  outputs.targetGuided ∪ outputs.corpusWide

theorem hybrid_exact_union (outputs : SearchModeOutputs Program Target) :
    outputs.hybrid = outputs.targetGuided ∪ outputs.corpusWide := rfl

theorem targetGuided_coverage_le_hybrid
    (outputs : SearchModeOutputs Program Target) :
    targetCoverage outputs.targetGuided ≤ targetCoverage outputs.hybrid := by
  apply targetCoverage_mono
  intro edge hedge
  exact Finset.mem_union_left _ hedge

theorem corpusWide_coverage_le_hybrid
    (outputs : SearchModeOutputs Program Target) :
    targetCoverage outputs.corpusWide ≤ targetCoverage outputs.hybrid := by
  apply targetCoverage_mono
  intro edge hedge
  exact Finset.mem_union_right _ hedge

theorem hybrid_target_inclusionExclusion
    (outputs : SearchModeOutputs Program Target) :
    targetCoverage outputs.hybrid +
        (sharedTargets outputs.targetGuided outputs.corpusWide).card =
      targetCoverage outputs.targetGuided +
        targetCoverage outputs.corpusWide :=
  target_inclusion_exclusion outputs.targetGuided outputs.corpusWide

theorem hybrid_programWitness_inclusionExclusion
    (outputs : SearchModeOutputs Program Target) :
    programCoverage outputs.hybrid +
        (sharedPrograms outputs.targetGuided outputs.corpusWide).card =
      programCoverage outputs.targetGuided +
        programCoverage outputs.corpusWide :=
  program_inclusion_exclusion outputs.targetGuided outputs.corpusWide

end SearchModeOutputs

/-- Equal standalone target yield can hide strictly different hybrid value. -/
theorem equal_standalone_yield_does_not_determine_hybrid_value :
    iidExpectedBipartiteTargetCoverage redundantArm 1 =
        iidExpectedBipartiteTargetCoverage complementaryArm 1 ∧
      twoArmExpectedBipartiteTargetUnionCoverage redundantArm 1 redundantArm 1 <
        twoArmExpectedBipartiteTargetUnionCoverage redundantArm 1 complementaryArm 1 :=
  equal_standalone_different_portfolio_value

/-- Negative finite-budget boundary: assigning half of a fixed budget to an
unproductive second arm can strictly reduce expected exact coverage relative
to spending the full budget on the best arm. -/
theorem hybrid_has_no_unconditional_finiteBudget_improvement :
    twoArmExpectedUnionCoverage bestPortfolioPrior 1
        unproductivePortfolioPrior 1 portfolioAccepted <
      iidExpectedDistinctCoverage bestPortfolioPrior 2 portfolioAccepted :=
  fixedSplit_strictly_loses_to_bestSingle

/-- What remains unconditional is fair baseline reachability: every baseline
rank has the explicit periodic submission time proved by the scheduler. -/
theorem hybrid_guidance_preserves_baseline_rank
    {Candidate : Type*} (baseline semantic : List Candidate)
    (semanticSlots rank : ℕ) :
    twoQueueCandidate baseline semantic semanticSlots
        (queuePeriod semanticSlots * rank) = baseline[rank]? :=
  twoQueueCandidate_mul_queuePeriod baseline semantic semanticSlots rank

#print axioms SearchModeOutputs.targetGuided_coverage_le_hybrid
#print axioms SearchModeOutputs.corpusWide_coverage_le_hybrid
#print axioms SearchModeOutputs.hybrid_target_inclusionExclusion
#print axioms equal_standalone_yield_does_not_determine_hybrid_value
#print axioms hybrid_has_no_unconditional_finiteBudget_improvement
#print axioms hybrid_guidance_preserves_baseline_rank

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping
