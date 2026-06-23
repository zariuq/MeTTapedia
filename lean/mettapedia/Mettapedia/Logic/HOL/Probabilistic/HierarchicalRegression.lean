import Mettapedia.Logic.HOL.Probabilistic.BenchmarkBridge
import Mettapedia.Logic.HOL.Probabilistic.Regression

/-!
# Hierarchical Regression Surface for Probabilistic HOL

This module packages the first positive and negative regression fixtures for the
hierarchical and infinite-order `ProbHOL` layer.

The intended reading follows the Kyburg/Gaifman/Atkinson line:

- semantic truth of HOL formulas remains primary,
- hierarchical uncertainty lives over measures on indexed model spaces,
- flattening recovers ordinary sentence probabilities,
- and empirical/counting semantics is then obtained as a theorem-proved
  special case.

The benchmark bridge remains a concrete finite instance of the same semantic
pattern, not a replacement for the general hierarchy.
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Probabilistic.HierarchicalState
open Mettapedia.Logic.PLNGuardedHigherOrderSemantics
open scoped ENNReal

noncomputable abbrev natFlagGeometricMeasure : MeasureTheory.Measure natFlagSpace.Idx :=
  (ProbabilityTheory.geometricMeasure halfUnitInterval :
    MeasureTheory.Measure natFlagSpace.Idx)

noncomputable instance : MeasureTheory.IsProbabilityMeasure natFlagGeometricMeasure := by
  change @MeasureTheory.IsProbabilityMeasure Nat Nat.instMeasurableSpace
    (ProbabilityTheory.geometricMeasure halfUnitInterval)
  exact ProbabilityTheory.isProbabilityMeasure_geometricMeasure

local instance instHierarchicalRegressionEmpiricalMeasurableSpace :
    MeasurableSpace (HenkinModel FixtureBase FixtureConst) := ⊤

private theorem empiricalPair_ne_zero : empiricalPair ≠ 0 := by
  simp [empiricalPair]

noncomputable abbrev empiricalPairModelSpace : ModelSpace FixtureBase FixtureConst :=
  empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair

noncomputable abbrev empiricalPairMeasure :
    MeasureTheory.Measure empiricalPairModelSpace.Idx :=
  (PMF.ofMultiset empiricalPair empiricalPair_ne_zero).toMeasure

noncomputable instance : MeasureTheory.IsProbabilityMeasure empiricalPairMeasure := by
  classical
  change @MeasureTheory.IsProbabilityMeasure
    (HenkinModel FixtureBase FixtureConst)
    empiricalPairModelSpace.instMeasurableSpace
    (PMF.ofMultiset empiricalPair empiricalPair_ne_zero).toMeasure
  exact PMF.toMeasure.isProbabilityMeasure
    (PMF.ofMultiset empiricalPair empiricalPair_ne_zero)

/-- Positive infinitary canary: the hierarchical constant-measure special case
recovers the existing `Nat`-indexed geometric regression exactly. -/
theorem hierarchical_regression_nat_geometric_flag_half :
    hierarchicalSentenceProb
        (HierarchicalState.ofConstantMeasure natFlagSpace natFlagGeometricMeasure)
        flagSentence =
      (1 / 2 : ℝ≥0∞) := by
  rw [hierarchicalSentenceProb_ofConstantMeasure_eq_sentenceProb]
  simpa [natFlagGeometricMeasure] using regression_nat_geometric_flag_half

/-- Negative infinitary canary: the same hierarchical geometric state does not
force the query with probability `1`. -/
theorem hierarchical_regression_nat_geometric_flag_ne_one :
    hierarchicalSentenceProb
        (HierarchicalState.ofConstantMeasure natFlagSpace natFlagGeometricMeasure)
        flagSentence ≠ 1 := by
  rw [hierarchical_regression_nat_geometric_flag_half]
  norm_num

/-- Positive compatibility chain: the empirical multiset semantics sits inside
the hierarchical layer via the constant-measure special case. -/
theorem hierarchical_regression_empirical_probStrength_eq_static :
    hierarchicalProbQueryStrength
        (HierarchicalState.ofConstantMeasure
          empiricalPairModelSpace
          empiricalPairMeasure)
        flagSentence =
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryStrength
        (State := Multiset (HenkinModel FixtureBase FixtureConst))
        (Query := Mettapedia.Logic.HOL.WorldModel.HOLQuery FixtureConst)
        empiricalPair
        flagSentence := by
  rw [hierarchicalProbQueryStrength_eq_sentenceProb,
    hierarchicalSentenceProb_ofConstantMeasure_eq_sentenceProb]
  exact empiricalSentenceProb_eq_staticQueryStrength
    (Base := FixtureBase) (Const := FixtureConst)
    empiricalPair empiricalPair_ne_zero flagSentence

/-- Concrete guarded benchmark payload used to witness the finite hierarchical
bridge: exact branch succeeds, fallback branch fails, bounded branch is mixed. -/
def regressionBenchmarkPayload : HigherOrderGuardPayload where
  weights :=
    { exactMass := (1 / 2 : ℚ)
      boundedMass := (1 / 3 : ℚ)
      fallbackMass := (1 / 6 : ℚ) }
  exactBranchValue := 1
  boundedBranchValue := (1 / 2 : ℚ)
  fallbackBranchValue := 0

theorem regressionBenchmarkPayload_valid :
    ValidBenchmarkPayload01 regressionBenchmarkPayload := by
  constructor
  · dsimp [ValidGuardRegimeWeights, regressionBenchmarkPayload]
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · norm_num [regressionBenchmarkPayload]
  · norm_num [regressionBenchmarkPayload]
  · norm_num [regressionBenchmarkPayload]
  · norm_num [regressionBenchmarkPayload]
  · norm_num [regressionBenchmarkPayload]
  · norm_num [regressionBenchmarkPayload]

/-- Positive benchmark canary: one latent regime component of the hierarchical
benchmark matches the declared exact branch value. -/
theorem hierarchical_regression_benchmark_exact_component_one :
    (benchmarkHierarchicalState regressionBenchmarkPayload regressionBenchmarkPayload_valid).componentSentenceProb
        GuardRegime.exactAdmissible benchmarkSentence =
      1 := by
  rw [componentSentenceProb_eq_branchMass]
  simp [branchMass, regressionBenchmarkPayload]

/-- Negative benchmark canary: another latent component matches the declared
fallback branch value and therefore gives zero query probability. -/
theorem hierarchical_regression_benchmark_fallback_component_zero :
    (benchmarkHierarchicalState regressionBenchmarkPayload regressionBenchmarkPayload_valid).componentSentenceProb
        GuardRegime.fallbackRequired benchmarkSentence =
      0 := by
  rw [componentSentenceProb_eq_branchMass]
  simp [branchMass, regressionBenchmarkPayload]

/-- The guarded benchmark payload is interpreted by flattening the hierarchy to
the predictive marginal over the benchmark query. -/
theorem hierarchical_regression_benchmark_flattening :
    hierarchicalSentenceProb
        (benchmarkHierarchicalState regressionBenchmarkPayload regressionBenchmarkPayload_valid)
        benchmarkSentence =
      ∫⁻ g, branchMass regressionBenchmarkPayload g
        ∂(benchmarkMixingPMF regressionBenchmarkPayload.weights
          regressionBenchmarkPayload_valid.validWeights).toMeasure := by
  exact benchmarkHierarchicalSentenceProb_eq_integral_branchMass
    regressionBenchmarkPayload regressionBenchmarkPayload_valid

end Mettapedia.Logic.HOL.Probabilistic
