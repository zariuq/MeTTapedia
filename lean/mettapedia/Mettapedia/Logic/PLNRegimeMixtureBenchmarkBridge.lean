import Mathlib.Data.Real.Basic
import Mettapedia.Logic.PLNRegimeMixtureTheorems
import Mettapedia.Logic.PLNProbHOLPlannerBridge

/-!
# Regime-Mixture Benchmark Bridge

This module instantiates the abstract finite regime-mixture theorem family on
the existing higher-order guarded benchmark payloads.

The architecture follows the council-approved layering:

- `PLNRegimeMixtureTheorems.lean` provides the abstract finite-regime theorems,
- `HOL/Probabilistic/BenchmarkBridge.lean` gives the semantic `ProbHOL` view,
- `HOL/Probabilistic/BenchmarkBeliefBridge.lean` gives the LI-style belief
  shadow,
- this file proves that the benchmark payloads are concrete instances of the
  abstract regime-mixture semantics.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.PLNGuardedHigherOrderSemantics
open Mettapedia.Logic.PLNMixedModeChainComposition
open Mettapedia.Logic.HOL.LogicalInduction
open Mettapedia.Logic.HOL.Probabilistic
open Mettapedia.Logic.PLNRegimeMixtureTheorems
open scoped ENNReal

/-- Real-valued posterior weights extracted from a guarded benchmark payload. -/
def benchmarkWeightsReal (payload : HigherOrderGuardPayload) : GuardRegime → ℝ
  | .exactAdmissible => payload.weights.exactMass
  | .boundedViolation => payload.weights.boundedMass
  | .fallbackRequired => payload.weights.fallbackMass

/-- Real-valued branch query values extracted from a guarded benchmark payload. -/
def benchmarkBranchValuesReal (payload : HigherOrderGuardPayload) : GuardRegime → ℝ
  | .exactAdmissible => payload.exactBranchValue
  | .boundedViolation => payload.boundedBranchValue
  | .fallbackRequired => payload.fallbackBranchValue

/-- The benchmark payload satisfies the abstract finite-regime weight axioms
after casting its rational masses to `ℝ`. -/
theorem benchmarkWeightsReal_valid
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    ValidRegimeWeights (benchmarkWeightsReal payload) := by
  rcases hvalid.validWeights with ⟨hexact, hbounded, hfallback, hsum⟩
  constructor
  · intro r
    cases r with
    | exactAdmissible =>
        simpa [benchmarkWeightsReal] using
          (show (0 : ℝ) ≤ (payload.weights.exactMass : ℝ) by exact_mod_cast hexact)
    | boundedViolation =>
        simpa [benchmarkWeightsReal] using
          (show (0 : ℝ) ≤ (payload.weights.boundedMass : ℝ) by exact_mod_cast hbounded)
    | fallbackRequired =>
        simpa [benchmarkWeightsReal] using
          (show (0 : ℝ) ≤ (payload.weights.fallbackMass : ℝ) by exact_mod_cast hfallback)
  · simp [benchmarkWeightsReal]
    have huniv :
        (Finset.univ : Finset GuardRegime) =
          { .exactAdmissible, .boundedViolation, .fallbackRequired } := by
      ext g
      cases g <;> simp
    rw [huniv]
    simp
    simpa [add_assoc] using
      (show
        ((payload.weights.exactMass : ℝ) +
            (payload.weights.boundedMass : ℝ) +
            (payload.weights.fallbackMass : ℝ) = 1) by
          exact_mod_cast hsum)

/-- Every benchmark branch value lies in the unit interval after casting to
`ℝ`. -/
theorem benchmarkBranchValuesReal_unitInterval
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    ∀ r, 0 ≤ benchmarkBranchValuesReal payload r ∧ benchmarkBranchValuesReal payload r ≤ 1 := by
  intro r
  cases r with
  | exactAdmissible =>
      exact ⟨by
          simpa [benchmarkBranchValuesReal] using
            (show (0 : ℝ) ≤ (payload.exactBranchValue : ℝ) by exact_mod_cast hvalid.exact_nonneg),
        by
          simpa [benchmarkBranchValuesReal] using
            (show (payload.exactBranchValue : ℝ) ≤ 1 by exact_mod_cast hvalid.exact_le_one)⟩
  | boundedViolation =>
      exact ⟨by
          simpa [benchmarkBranchValuesReal] using
            (show (0 : ℝ) ≤ (payload.boundedBranchValue : ℝ) by exact_mod_cast hvalid.bounded_nonneg),
        by
          simpa [benchmarkBranchValuesReal] using
            (show (payload.boundedBranchValue : ℝ) ≤ 1 by exact_mod_cast hvalid.bounded_le_one)⟩
  | fallbackRequired =>
      exact ⟨by
          simpa [benchmarkBranchValuesReal] using
            (show (0 : ℝ) ≤ (payload.fallbackBranchValue : ℝ) by exact_mod_cast hvalid.fallback_nonneg),
        by
          simpa [benchmarkBranchValuesReal] using
            (show (payload.fallbackBranchValue : ℝ) ≤ 1 by exact_mod_cast hvalid.fallback_le_one)⟩

/-- The abstract mixture value agrees exactly with the guarded benchmark's
flattened higher-order semantic value after casting to `ℝ`. -/
theorem benchmarkMixtureValue_eq_higherOrderSemanticValue
    (payload : HigherOrderGuardPayload) :
    mixtureValue (benchmarkWeightsReal payload) (benchmarkBranchValuesReal payload) =
      (higherOrderSemanticValue payload : ℝ) := by
  unfold mixtureValue benchmarkWeightsReal benchmarkBranchValuesReal higherOrderSemanticValue
  have huniv :
      (Finset.univ : Finset GuardRegime) =
        { .exactAdmissible, .boundedViolation, .fallbackRequired } := by
    ext g
    cases g <;> simp
  rw [huniv]
  simp
  ring

/-- The benchmark belief price is exactly the abstract mixture value. -/
theorem benchmarkMixtureValue_eq_benchmarkBeliefPrice
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    mixtureValue (benchmarkWeightsReal payload) (benchmarkBranchValuesReal payload) =
      (benchmarkBeliefPrice payload hvalid : Rat) := by
  rw [benchmarkBeliefPrice_val]
  exact benchmarkMixtureValue_eq_higherOrderSemanticValue payload

/-- The semantic benchmark hierarchy answers the benchmark sentence by the same
mixture value as the abstract finite-regime semantics. -/
theorem benchmarkHierarchicalSentenceProb_eq_ofReal_benchmarkMixtureValue
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    hierarchicalSentenceProb
        (benchmarkHierarchicalState payload hvalid)
        benchmarkSentence =
      ENNReal.ofReal (mixtureValue (benchmarkWeightsReal payload) (benchmarkBranchValuesReal payload)) := by
  rw [benchmarkHierarchicalSentenceProb_eq_higherOrderSemanticValue]
  rw [benchmarkMixtureValue_eq_higherOrderSemanticValue]

/-- The benchmark shadow's carried value is the guarded benchmark's flattened
value, which is the rational source behind the abstract real-valued mixture. -/
theorem benchmarkPlannerShadow_carried_value_eq_higherOrderSemanticValue
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    (benchmarkPlannerShadow query payload hvalid sigma provenance).carried.value =
      some (higherOrderSemanticValue payload) := by
  rw [benchmarkPlannerShadow_carried_value_eq_benchmarkBeliefPrice]
  rw [benchmarkBeliefPrice_val]

/-- The exact-branch direct continuation error obeys the abstract residual-mass
bound. -/
theorem benchmarkDirectApprox_exactBranch_bound
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    |mixtureValue (benchmarkWeightsReal payload) (benchmarkBranchValuesReal payload)
        - benchmarkBranchValuesReal payload .exactAdmissible| ≤
      (1 - benchmarkWeightsReal payload .exactAdmissible) *
        branchRadius (benchmarkBranchValuesReal payload) .exactAdmissible := by
  simpa using
    directApprox_error_le_residualMass_mul_branchRadius
      (w := benchmarkWeightsReal payload)
      (q := benchmarkBranchValuesReal payload)
      (hw := benchmarkWeightsReal_valid payload hvalid)
      .exactAdmissible

/-- The mixture predictor weakly dominates the exact-branch predictor under
squared loss. -/
theorem benchmarkMixtureSquaredLoss_le_exactBranchRisk
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    mixtureVariance (benchmarkWeightsReal payload) (benchmarkBranchValuesReal payload) ≤
      expectedSquaredLoss
        (benchmarkWeightsReal payload)
        (benchmarkBranchValuesReal payload)
        (benchmarkBranchValuesReal payload .exactAdmissible) := by
  simpa using
    expectedSquaredLoss_mixture_le
      (w := benchmarkWeightsReal payload)
      (q := benchmarkBranchValuesReal payload)
      (hw := benchmarkWeightsReal_valid payload hvalid)
      (benchmarkBranchValuesReal payload .exactAdmissible)

/-- Reveal gain in the benchmark bridge is exactly the abstract
variance-minus-cost expression. -/
def benchmarkRevealGain
    (payload : HigherOrderGuardPayload)
    (c : ℝ) : ℝ :=
  revealGain (benchmarkWeightsReal payload) (benchmarkBranchValuesReal payload) c

theorem benchmarkRevealGain_eq_variance_minus_cost
    (payload : HigherOrderGuardPayload)
    (c : ℝ) :
    benchmarkRevealGain payload c =
      mixtureVariance (benchmarkWeightsReal payload) (benchmarkBranchValuesReal payload) - c := by
  rfl

/-- Reveal is preferred to the mixture predictor once reveal cost is below the
mixture variance. -/
theorem benchmarkRevealPreferred_if_cost_lt_variance
    (payload : HigherOrderGuardPayload)
    (c : ℝ)
    (hc : c < mixtureVariance (benchmarkWeightsReal payload) (benchmarkBranchValuesReal payload)) :
    0 < benchmarkRevealGain payload c := by
  simpa [benchmarkRevealGain] using
    revealPreferred_if_cost_lt_variance
      (w := benchmarkWeightsReal payload)
      (q := benchmarkBranchValuesReal payload)
      hc

/-- Concrete direct-approximation bound for the leaky higher-order benchmark
fixture already used in the planner demos. -/
theorem leaky_regimeMixture_directApprox_exactBranch_bound :
    |mixtureValue
        (benchmarkWeightsReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload)
        - benchmarkBranchValuesReal leakyHigherOrderPayload .exactAdmissible| ≤
      (1 - benchmarkWeightsReal leakyHigherOrderPayload .exactAdmissible) *
        branchRadius (benchmarkBranchValuesReal leakyHigherOrderPayload) .exactAdmissible := by
  exact benchmarkDirectApprox_exactBranch_bound
    leakyHigherOrderPayload leakyHigherOrderPayload_valid01

/-- Concrete squared-loss dominance of the mixture predictor over direct exact
continuation on the leaky fixture. -/
theorem leaky_regimeMixture_mixtureSquaredLoss_le_exactBranchRisk :
    mixtureVariance
        (benchmarkWeightsReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload) ≤
      expectedSquaredLoss
        (benchmarkWeightsReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload)
        (benchmarkBranchValuesReal leakyHigherOrderPayload .exactAdmissible) := by
  exact benchmarkMixtureSquaredLoss_le_exactBranchRisk
    leakyHigherOrderPayload leakyHigherOrderPayload_valid01

end Mettapedia.Logic
