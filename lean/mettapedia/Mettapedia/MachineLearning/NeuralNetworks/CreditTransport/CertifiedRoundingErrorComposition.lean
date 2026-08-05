import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedIntervalEvaluation

/-!
# Certified composition of approximation and rounding error

This file reconstructs and generalizes the error-composition rules from
de Dinechin, Lauter, and Melquiond, *Certifying the Floating-Point
Implementation of an Elementary Function Using Gappa* (2008), Sections
3.1--3.5.

The source represents rounding as a real-to-real operation, encloses absolute
errors after rewriting

`computed - exact = (computed - approximate) + (approximate - exact)`,

and represents relative error multiplicatively so that the exact reference
may be zero.  Two relative stages compose with the indispensable cross term

`roundingError + approximationError +
  roundingError * approximationError`.

The definitions below retain asymmetric interval bounds and reuse the
kernel-checked endpoint operations from `CertifiedIntervalEvaluation`.
Multiple valid evaluation paths may be intersected.  Positive fixtures recover
the exact composition identities, while negative fixtures show that dropping
the cross term is unsound and that division by a zero reference loses the
information retained by the multiplicative predicate.

This module does not claim that a particular runtime implements IEEE-754
rounding.  Such a connection requires an authenticated implementation-specific
certificate supplying the local error enclosure.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CertifiedRoundingErrorComposition

noncomputable section

open CertifiedIntervalEvaluation

open CertifiedIntervalEvaluation.ClosedInterval

/-- An asymmetric interval enclosure of the absolute error
`computed - exact`. -/
def AbsoluteErrorEnclosure
    (computed exact : Real) (errorInterval : ClosedInterval) : Prop :=
  errorInterval.Contains (computed - exact)

/-- The zero-safe relative-error predicate used by Gappa.

The witness equation is meaningful even when `exact = 0`.  The lower-endpoint
condition matches the source predicate and rules out a relative factor that
can cross or reach `-1`. -/
def RelativeErrorEnclosure
    (computed exact : Real) (errorInterval : ClosedInterval) : Prop :=
  -1 < errorInterval.lower ∧
    ∃ error, errorInterval.Contains error ∧
      computed = exact * (1 + error)

/-- The exact relative-error interval produced by the source's two-stage
rewrite: `rounding + approximation + rounding * approximation`. -/
def composeRelativeIntervals
    (rounding approximation : ClosedInterval) : ClosedInterval :=
  .add (.add rounding approximation) (.multiply rounding approximation)

/-- Intersection of two independently justified interval paths.  Improper
endpoints represent an empty intersection. -/
def intersectIntervals
    (left right : ClosedInterval) : ClosedInterval :=
  ⟨max left.lower right.lower, min left.upper right.upper⟩

theorem contains_intersectIntervals_iff
    {left right : ClosedInterval} {value : Real} :
    (intersectIntervals left right).Contains value ↔
      left.Contains value ∧ right.Contains value := by
  simp only [intersectIntervals, ClosedInterval.Contains, max_le_iff,
    le_min_iff]
  aesop

/-- Absolute rounding error and approximation error add exactly. -/
theorem absolute_error_compose
    {computed approximate exact : Real}
    {roundingInterval approximationInterval : ClosedInterval}
    (rounding :
      AbsoluteErrorEnclosure computed approximate roundingInterval)
    (approximation :
      AbsoluteErrorEnclosure approximate exact approximationInterval) :
    AbsoluteErrorEnclosure computed exact
      (ClosedInterval.add roundingInterval approximationInterval) := by
  have enclosed := ClosedInterval.contains_add rounding approximation
  change
    (ClosedInterval.add roundingInterval approximationInterval).Contains
      (computed - exact)
  convert enclosed using 1
  ring

/-- A multiplicative relative enclosure implies the corresponding absolute
enclosure once the exact value itself has an interval. -/
theorem relative_to_absolute
    {computed exact : Real}
    {exactInterval errorInterval : ClosedInterval}
    (exactMembership : exactInterval.Contains exact)
    (relative :
      RelativeErrorEnclosure computed exact errorInterval) :
    AbsoluteErrorEnclosure computed exact
      (ClosedInterval.multiply exactInterval errorInterval) := by
  rcases relative.2 with ⟨error, errorMembership, equation⟩
  have enclosed :=
    ClosedInterval.contains_multiply exactMembership errorMembership
  change
    (ClosedInterval.multiply exactInterval errorInterval).Contains
      (computed - exact)
  convert enclosed using 1
  rw [equation]
  ring

/-- The source's relative-error rewrite, including the product term.  The
resulting interval must itself satisfy the source predicate's lower-endpoint
side condition; endpoint interval evaluation can be looser than the actual
positive multiplicative factors. -/
theorem relative_error_compose
    {computed approximate exact : Real}
    {roundingInterval approximationInterval : ClosedInterval}
    (rounding :
      RelativeErrorEnclosure computed approximate roundingInterval)
    (approximation :
      RelativeErrorEnclosure approximate exact approximationInterval)
    (totalLower :
      -1 <
        (composeRelativeIntervals
          roundingInterval approximationInterval).lower) :
    RelativeErrorEnclosure computed exact
      (composeRelativeIntervals roundingInterval approximationInterval) := by
  rcases rounding.2 with
    ⟨roundingError, roundingMembership, roundingEquation⟩
  rcases approximation.2 with
    ⟨approximationError, approximationMembership, approximationEquation⟩
  refine ⟨totalLower, ?_⟩
  let totalError :=
    roundingError + approximationError +
      roundingError * approximationError
  refine ⟨totalError, ?_, ?_⟩
  · have sumMembership :=
      ClosedInterval.contains_add roundingMembership approximationMembership
    have productMembership :=
      ClosedInterval.contains_multiply
        roundingMembership approximationMembership
    exact ClosedInterval.contains_add sumMembership productMembership
  · dsimp [totalError]
    rw [roundingEquation, approximationEquation]
    ring

/-- The multiplicative predicate remains informative at a zero exact value:
it forces the computed value to be zero. -/
theorem relative_error_at_zero_forces_computed_zero
    {computed : Real} {errorInterval : ClosedInterval}
    (relative :
      RelativeErrorEnclosure computed 0 errorInterval) :
    computed = 0 := by
  rcases relative.2 with ⟨error, _, equation⟩
  simpa using equation

/-- Exact zero satisfies the zero-safe relative predicate whenever zero lies
in the declared error interval and the source lower-bound condition holds. -/
theorem zero_relative_error_enclosed
    {errorInterval : ClosedInterval}
    (lower : -1 < errorInterval.lower)
    (zeroMembership : errorInterval.Contains 0) :
    RelativeErrorEnclosure 0 0 errorInterval := by
  exact ⟨lower, 0, zeroMembership, by ring⟩

/-- Independently justified interval paths may be intersected without losing
the enclosed error. -/
theorem intersect_absolute_error_paths
    {computed exact : Real} {left right : ClosedInterval}
    (leftPath : AbsoluteErrorEnclosure computed exact left)
    (rightPath : AbsoluteErrorEnclosure computed exact right) :
    AbsoluteErrorEnclosure computed exact (intersectIntervals left right) := by
  exact contains_intersectIntervals_iff.mpr ⟨leftPath, rightPath⟩

/-- An improper intersection proves that no real value satisfies both input
enclosures. -/
theorem no_common_value_of_improper_intersection
    {left right : ClosedInterval}
    (improper :
      (intersectIntervals left right).upper <
        (intersectIntervals left right).lower) :
    ¬ ∃ value, left.Contains value ∧ right.Contains value := by
  rintro ⟨value, leftMembership, rightMembership⟩
  have intersectionMembership :
      (intersectIntervals left right).Contains value :=
    contains_intersectIntervals_iff.mpr
      ⟨leftMembership, rightMembership⟩
  exact (not_lt_of_ge
    (intersectionMembership.1.trans intersectionMembership.2)) improper

/-! ## Positive and negative fixtures -/

private def oneTenth : Real := 1 / 10

private def idealValue : Real := 1

private def approximateValue : Real := 11 / 10

private def computedValue : Real := 121 / 100

private def oneTenthInterval : ClosedInterval :=
  .point oneTenth

/-- Both stages in the concrete fixture have exact relative error `1/10`. -/
theorem two_stage_fixture_local_errors :
    RelativeErrorEnclosure approximateValue idealValue oneTenthInterval ∧
    RelativeErrorEnclosure computedValue approximateValue oneTenthInterval := by
  constructor
  · refine ⟨?_, oneTenth, ?_, ?_⟩
    · norm_num [oneTenthInterval, oneTenth, ClosedInterval.point]
    · norm_num [oneTenthInterval, oneTenth, ClosedInterval.point,
        ClosedInterval.Contains]
    · norm_num [approximateValue, idealValue, oneTenth]
  · refine ⟨?_, oneTenth, ?_, ?_⟩
    · norm_num [oneTenthInterval, oneTenth, ClosedInterval.point]
    · norm_num [oneTenthInterval, oneTenth, ClosedInterval.point,
        ClosedInterval.Contains]
    · norm_num [computedValue, approximateValue, oneTenth]

/-- The certified composition retains the exact total relative error
`21/100`. -/
theorem two_stage_fixture_composed :
    RelativeErrorEnclosure computedValue idealValue
      (composeRelativeIntervals oneTenthInterval oneTenthInterval) := by
  apply relative_error_compose
  · exact two_stage_fixture_local_errors.2
  · exact two_stage_fixture_local_errors.1
  · norm_num [composeRelativeIntervals, oneTenthInterval, oneTenth,
      ClosedInterval.point, ClosedInterval.add, ClosedInterval.multiply,
      ClosedInterval.productLower, ClosedInterval.productUpper]

/-- Dropping the product term would claim total relative error `1/5`; the
actual two-stage computation has error `21/100`, so that claim is false. -/
theorem dropping_relative_cross_term_is_unsound :
    ¬ RelativeErrorEnclosure computedValue idealValue
      (.point (1 / 5)) := by
  rintro ⟨_, error, membership, equation⟩
  have error_eq : error = (1 / 5 : Real) :=
    le_antisymm membership.2 membership.1
  rw [error_eq] at equation
  norm_num [computedValue, idealValue] at equation

/-- Field division at a zero reference evaluates to zero in Lean even for a
nonzero discrepancy, while the multiplicative predicate correctly rejects the
same pair.  This is why the source does not define relative error by division. -/
theorem division_form_loses_zero_reference_information :
    (((1 : Real) - 0) / 0 = 0) ∧
    ¬ RelativeErrorEnclosure 1 0 (.point 0) := by
  constructor
  · norm_num
  · intro relative
    exact one_ne_zero (relative_error_at_zero_forces_computed_zero relative)

/-- Intersecting two valid paths can strictly improve an absolute-error
enclosure. -/
theorem intersected_paths_strictly_narrower :
    let coarse : ClosedInterval := ⟨-1, 2⟩
    let refined : ClosedInterval := ⟨-(1 / 2), 1⟩
    let value : Real := 1 / 4
    (intersectIntervals coarse refined).Contains value ∧
      (intersectIntervals coarse refined).width < coarse.width := by
  norm_num [intersectIntervals, ClosedInterval.Contains,
    ClosedInterval.width]

#print axioms absolute_error_compose
#print axioms relative_to_absolute
#print axioms relative_error_compose
#print axioms relative_error_at_zero_forces_computed_zero
#print axioms intersect_absolute_error_paths
#print axioms dropping_relative_cross_term_is_unsound
#print axioms division_form_loses_zero_reference_information

end

end CertifiedRoundingErrorComposition

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
