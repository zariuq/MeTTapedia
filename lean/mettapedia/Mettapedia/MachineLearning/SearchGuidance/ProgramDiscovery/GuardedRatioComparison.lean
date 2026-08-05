import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.CostAwareOpportunityControl

/-!
# Guarded relative-coverage comparison

Cross-multiplied ratio comparison `a/b ≥ p/q` over naturals silently accepts
the `0/0` case, because both sides of `p * b ≤ q * a` vanish.  The guarded
predicate adds the positivity of the reference and is proved equivalent to
the unguarded comparison exactly when the reference is positive, monotone in
the candidate, and false at a zero reference.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

namespace AdaptivePortfolio

/-- A rational coverage threshold in `[0, 1]`, stored as exact natural-number
data. -/
structure RelativeCoverageThreshold where
  numerator : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator
  numerator_le_denominator : numerator ≤ denominator

/-- The exact three-quarters coverage threshold. -/
def threeQuarters : RelativeCoverageThreshold where
  numerator := 3
  denominator := 4
  denominator_pos := by norm_num
  numerator_le_denominator := by norm_num

/-- The unguarded cross-multiplied comparison, retained to expose the `0 / 0`
failure boundary. -/
def unguardedRelativeCoverageCheck
    (threshold : RelativeCoverageThreshold)
    (candidateCoverage referenceCoverage : ℕ) : Bool :=
  decide
    (threshold.numerator * referenceCoverage ≤
      threshold.denominator * candidateCoverage)

/-- Relative coverage is admissible evidence only when the reference coverage
is positive. -/
def MeetsGuardedRelativeCoverage
    (threshold : RelativeCoverageThreshold)
    (candidateCoverage referenceCoverage : ℕ) : Prop :=
  0 < referenceCoverage ∧
    threshold.numerator * referenceCoverage ≤
      threshold.denominator * candidateCoverage

instance
    (threshold : RelativeCoverageThreshold)
    (candidateCoverage referenceCoverage : ℕ) :
    Decidable
      (MeetsGuardedRelativeCoverage threshold
        candidateCoverage referenceCoverage) := by
  unfold MeetsGuardedRelativeCoverage
  infer_instance

/-- Executable guarded relative-coverage check. -/
def guardedRelativeCoverageCheck
    (threshold : RelativeCoverageThreshold)
    (candidateCoverage referenceCoverage : ℕ) : Bool :=
  decide
    (MeetsGuardedRelativeCoverage threshold
      candidateCoverage referenceCoverage)

theorem guardedRelativeCoverageCheck_eq_true_iff
    (threshold : RelativeCoverageThreshold)
    (candidateCoverage referenceCoverage : ℕ) :
    guardedRelativeCoverageCheck threshold
        candidateCoverage referenceCoverage = true ↔
      MeetsGuardedRelativeCoverage threshold
        candidateCoverage referenceCoverage := by
  simp [guardedRelativeCoverageCheck]

theorem guardedRelativeCoverageCheck_zero_reference
    (threshold : RelativeCoverageThreshold) (candidateCoverage : ℕ) :
    guardedRelativeCoverageCheck threshold candidateCoverage 0 = false := by
  simp [guardedRelativeCoverageCheck, MeetsGuardedRelativeCoverage]

theorem unguardedRelativeCoverageCheck_zero_zero
    (threshold : RelativeCoverageThreshold) :
    unguardedRelativeCoverageCheck threshold 0 0 = true := by
  simp [unguardedRelativeCoverageCheck]

/-- Once the reference coverage is positive, the guard changes no positive
comparison result. -/
theorem guarded_eq_unguarded_of_reference_pos
    (threshold : RelativeCoverageThreshold)
    (candidateCoverage referenceCoverage : ℕ)
    (reference_pos : 0 < referenceCoverage) :
    guardedRelativeCoverageCheck threshold
        candidateCoverage referenceCoverage =
      unguardedRelativeCoverageCheck threshold
        candidateCoverage referenceCoverage := by
  simp [guardedRelativeCoverageCheck, MeetsGuardedRelativeCoverage,
    unguardedRelativeCoverageCheck, reference_pos]

/-- Increasing candidate coverage cannot invalidate a guarded relative
coverage certificate. -/
theorem guardedRelativeCoverageCheck_mono_candidate
    (threshold : RelativeCoverageThreshold)
    {candidateCoverage candidateCoverage' referenceCoverage : ℕ}
    (candidate_le : candidateCoverage ≤ candidateCoverage')
    (accepted :
      guardedRelativeCoverageCheck threshold
        candidateCoverage referenceCoverage = true) :
    guardedRelativeCoverageCheck threshold
        candidateCoverage' referenceCoverage = true := by
  rw [guardedRelativeCoverageCheck_eq_true_iff] at accepted ⊢
  constructor
  · exact accepted.1
  · exact le_trans accepted.2
      (Nat.mul_le_mul_left threshold.denominator candidate_le)

section Examples

/-- Three accepted targets meet three quarters of a four-target reference. -/
theorem three_of_four :
    guardedRelativeCoverageCheck threeQuarters 3 4 = true := by
  decide

/-- Two accepted targets do not meet three quarters of a four-target
reference. -/
theorem two_of_four :
    guardedRelativeCoverageCheck threeQuarters 2 4 = false := by
  decide

end Examples

#print axioms guardedRelativeCoverageCheck_eq_true_iff
#print axioms guardedRelativeCoverageCheck_zero_reference
#print axioms unguardedRelativeCoverageCheck_zero_zero
#print axioms guarded_eq_unguarded_of_reference_pos
#print axioms guardedRelativeCoverageCheck_mono_candidate
#print axioms three_of_four
#print axioms two_of_four

end AdaptivePortfolio

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
