import Mettapedia.MachineLearning.SearchGuidance.SharpnessPortfolio

/-!
# Budgeted distinct-coverage yield certificate

This file packages the exact fixed-i.i.d. results for ranking quality,
collisions, sharpness, and portfolio allocation into one certificate.  The
scope is deliberately finite fixed-prior sampling.  Sequential/adaptive
sampling requires a filtration or history-indexed kernel and is not licensed
by this certificate.
-/

noncomputable section

namespace Mettapedia.MachineLearning.SearchGuidance

open Finset BigOperators
open Mettapedia.ProbabilityTheory.Exchangeability.CategoricalDeFinetti

/-- A certificate collecting the four operational levers of fixed-budget
distinct verified yield, together with counterexamples preventing any
assumption-free dominance claim.  Every field refers to an expectation over
the actual finite categorical word model. -/
structure BudgetedSearchYieldCertificate : Prop where
  exactDistinctCoverage :
    ∀ {k : ℕ} (θ : ProbSimplex k) (budget : ℕ)
        (accepted : Finset (Fin k)),
      iidExpectedDistinctCoverage θ budget accepted =
        ∑ target ∈ accepted,
          (1 - (1 - (θ : Fin k → ℝ) target) ^ budget)
  rankingQualitySeparation :
    ∀ budget : ℕ, 0 < budget →
      targetSetMass lowTargetMassPrior {1} <
          targetSetMass highTargetMassPrior {1} ∧
        categoricalEntropy lowTargetMassPrior =
          categoricalEntropy highTargetMassPrior ∧
        iidExpectedDistinctCoverage lowTargetMassPrior budget {1} <
          iidExpectedDistinctCoverage highTargetMassPrior budget {1}
  pairCollisionExact :
    ∀ {k : ℕ} (θ : ProbSimplex k),
      (∑ xs : Fin 2 → Fin k,
        if xs 0 = xs 1 then
          categoricalProductPMF (θ : Fin k → ℝ) xs else 0) =
        collisionMass θ
  collisionMassNotSufficient :
    collisionMass halfHalfZeroPrior = collisionMass twoThirdsSixthsPrior ∧
      iidExpectedDistinctCoverage halfHalfZeroPrior 3 Finset.univ ≠
        iidExpectedDistinctCoverage twoThirdsSixthsPrior 3 Finset.univ
  duplicateAwareGain :
    ∀ {k : ℕ} (θ : ProbSimplex k) (hk : 2 ≤ k),
      (distinctVerifiedCoverage (firstTwoDistinctWord hk) Finset.univ : ℝ) -
          iidExpectedDistinctCoverage θ 2 Finset.univ =
        collisionMass θ
  canonicalPostprocessingBoundary :
    iidExpectedPostCanonicalCoverage 2 =
      iidExpectedDistinctCoverage (uniformPrior 2 (by norm_num)) 2 Finset.univ
  sharpnessInterior :
    iidExpectedDistinctCoverage (rankedPowerPrior 0) 2 rankedAccepted <
        iidExpectedDistinctCoverage (rankedPowerPrior 1) 2 rankedAccepted ∧
      iidExpectedDistinctCoverage (rankedPowerPrior 3) 2 rankedAccepted <
        iidExpectedDistinctCoverage (rankedPowerPrior 1) 2 rankedAccepted
  sharpnessNoUniversalDirection :
    ¬ Monotone (fun β : ℕ ↦
        iidExpectedDistinctCoverage (rankedPowerPrior β) 2 rankedAccepted) ∧
      ¬ Antitone (fun β : ℕ ↦
        iidExpectedDistinctCoverage (rankedPowerPrior β) 2 rankedAccepted)
  portfolioUnionDecomposition :
    ∀ {k : ℕ} (θ₁ : ProbSimplex k) (budget₁ : ℕ)
        (θ₂ : ProbSimplex k) (budget₂ : ℕ)
        (accepted : Finset (Fin k)),
      twoArmExpectedUnionCoverage θ₁ budget₁ θ₂ budget₂ accepted =
        twoArmExpectedSharedCoverage θ₁ budget₁ θ₂ budget₂ accepted +
          twoArmExpectedExclusiveLeftCoverage θ₁ budget₁ θ₂ budget₂
            accepted +
          twoArmExpectedExclusiveRightCoverage θ₁ budget₁ θ₂ budget₂
            accepted
  decorrelationRaisesActualExclusivity :
    ∀ {k : ℕ} (θ₁ θ₂ φ₁ φ₂ : ProbSimplex k)
        (accepted : Finset (Fin k)),
      targetSetMass θ₁ accepted = targetSetMass φ₁ accepted →
      targetSetMass θ₂ accepted = targetSetMass φ₂ accepted →
      acceptedPriorOverlap φ₁ φ₂ accepted <
          acceptedPriorOverlap θ₁ θ₂ accepted →
      twoArmExpectedExclusiveLeftCoverage θ₁ 1 θ₂ 1 accepted +
          twoArmExpectedExclusiveRightCoverage θ₁ 1 θ₂ 1 accepted <
        twoArmExpectedExclusiveLeftCoverage φ₁ 1 φ₂ 1 accepted +
          twoArmExpectedExclusiveRightCoverage φ₁ 1 φ₂ 1 accepted
  computableAllocationFixture :
    twoArmExpectedUnionCoverage bestPortfolioPrior 1
          unproductivePortfolioPrior 1 portfolioAccepted <
        twoArmExpectedUnionCoverage bestPortfolioPrior 2
          unproductivePortfolioPrior 0 portfolioAccepted ∧
      iidExpectedDistinctCoverage bestPortfolioPrior 2 portfolioAccepted =
        twoArmExpectedUnionCoverage bestPortfolioPrior 2
          unproductivePortfolioPrior 0 portfolioAccepted

/-- T5 certificate: in the finite fixed-i.i.d. checker model, distinct yield is
controlled jointly by accepted ranking mass, collision/repetition, temperature,
and allocation across complementary arms.  The collision, canonicalization,
sharpness, and fixed-split counterexamples are part of the certificate, so the
statement licenses no universal dominance claim outside its hypotheses. -/
theorem budgetedSearchYield : BudgetedSearchYieldCertificate := by
  refine
    { exactDistinctCoverage := ?_
      rankingQualitySeparation := ?_
      pairCollisionExact := ?_
      collisionMassNotSufficient := ?_
      duplicateAwareGain := ?_
      canonicalPostprocessingBoundary := ?_
      sharpnessInterior := ?_
      sharpnessNoUniversalDirection := ?_
      portfolioUnionDecomposition := ?_
      decorrelationRaisesActualExclusivity := ?_
      computableAllocationFixture := ?_ }
  · intro k θ budget accepted
    exact iidExpectedDistinctCoverage_eq_sum_one_sub_pow θ budget accepted
  · intro budget hbudget
    constructor
    · rw [targetSetMass_singleton, targetSetMass_singleton]
      change (1 / 4 : ℝ) < 3 / 4
      norm_num
    · exact equal_entropy_strictly_ordered_distinctYield budget hbudget
  · intro k θ
    exact twoDrawCollisionProbability_eq_collisionMass θ
  · exact equal_collisionMass_different_threeDrawCoverage
  · intro k θ hk
    exact twoDraw_duplicateFree_gain_eq_collisionMass θ hk
  · exact canonical_postprocessing_no_strict_gain
  · exact sharpness_has_interior_optimum
  · exact ⟨rankedPowerPrior_distinctCoverage_not_monotone,
      rankedPowerPrior_distinctCoverage_not_antitone⟩
  · intro k θ₁ budget₁ θ₂ budget₂ accepted
    exact twoArmExpectedUnionCoverage_decomposition
      θ₁ budget₁ θ₂ budget₂ accepted
  · intro k θ₁ θ₂ φ₁ φ₂ accepted hmass₁ hmass₂ hoverlap
    exact twoArmExpectedTotalExclusive_strict_of_overlap_lt
      θ₁ θ₂ φ₁ φ₂ accepted hmass₁ hmass₂ hoverlap
  · exact computableAllocation_dominates_split_and_single

#print axioms budgetedSearchYield

end Mettapedia.MachineLearning.SearchGuidance
