import Mettapedia.MachineLearning.ContinualLearning.LowRankForgettingGeometry

/-!
# Continual low-rank routing

C-LoRA inserts a square routing matrix between the two factors of a low-rank
adapter.  A routing matrix can express a mixture of low-rank experts as a
block-diagonal special case, while the decomposition

`routing = oldRouting + freshRouting`

preserves the complete forward value and permits the old path to be stopped
during differentiation.

This file recovers the exact algebra behind Equations (3)--(17) and (26) of
Zhang et al., *C-LoRA: Continual Low-Rank Adaptation for Pre-trained Models*
(2025).  The source's gradient comparison is generalized to the exact
condition it uses: the old and fresh gradient contributions must have
nonnegative Frobenius pairing, and the old contribution must be nonzero.
Under that condition, differentiating only the fresh route has strictly
smaller squared Frobenius magnitude.  An anti-aligned counterexample proves
that routing decomposition alone does not imply the comparison.

The orthogonality penalty is formalized as an entrywise squared norm.  Its
zero set is exactly the stated annihilation equation, with disjoint and
overlapping two-axis fixtures.  Finally, a finite-loss counterexample keeps
the theorem's scope honest: smaller parameter motion does not by itself imply
less forgetting for an arbitrary old-task loss.  The source's benchmark
accuracy and its claim that this mechanism reduces empirical forgetting
remain empirical.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

open scoped BigOperators InnerProductSpace

namespace ContinualLowRankRouting

noncomputable section

/-! ## Routing as a mixture of low-rank experts -/

variable {Expert LocalIndex Output Input : Type*}
  [Fintype Expert] [DecidableEq Expert]
  [Fintype LocalIndex] [DecidableEq LocalIndex]

/-- A block-diagonal routing matrix with one scalar weight per expert block. -/
def blockDiagonalRouting (weight : Expert → ℝ) :
    Matrix (Expert × LocalIndex) (Expert × LocalIndex) ℝ :=
  fun source target =>
    if source = target then weight source.1 else 0

/-- The low-rank branch represented by one contiguous expert block. -/
def expertBranch
    (left : Matrix Output (Expert × LocalIndex) ℝ)
    (right : Matrix (Expert × LocalIndex) Input ℝ)
    (expert : Expert) : Matrix Output Input ℝ :=
  fun outputIndex inputIndex =>
    ∑ localIndex,
      left outputIndex (expert, localIndex) *
        right (expert, localIndex) inputIndex

/-- Pointwise mixture of the expert blocks represented by shared factors. -/
def mixtureOfExperts
    (left : Matrix Output (Expert × LocalIndex) ℝ)
    (right : Matrix (Expert × LocalIndex) Input ℝ)
    (weight : Expert → ℝ) : Matrix Output Input ℝ :=
  fun outputIndex inputIndex =>
    ∑ expert,
      weight expert *
        expertBranch left right expert outputIndex inputIndex

/-- Source Equations (4)--(5): block-diagonal routing is exactly a weighted
mixture of the corresponding low-rank expert branches. -/
theorem blockDiagonalRouting_recovers_mixture
    (left : Matrix Output (Expert × LocalIndex) ℝ)
    (right : Matrix (Expert × LocalIndex) Input ℝ)
    (weight : Expert → ℝ) :
    ((left * blockDiagonalRouting weight) * right :
        Matrix Output Input ℝ) =
      mixtureOfExperts left right weight := by
  ext outputIndex inputIndex
  simp [Matrix.mul_apply, blockDiagonalRouting, mixtureOfExperts,
    expertBranch]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro expert _
  apply Finset.sum_congr rfl
  intro localIndex _
  ring

/-! ## Exact old/fresh decomposition -/

variable {Route : Type*} [Fintype Route]

/-- The routed low-rank weight delta. -/
def routedDelta
    (left : Matrix Output Route ℝ)
    (routing : Matrix Route Route ℝ)
    (right : Matrix Route Input ℝ) :
    Matrix Output Input ℝ :=
  (left * routing) * right

/-- Source Equations (11)--(12), at the value level: stopping the old route's
gradient does not remove its forward contribution. -/
theorem routedDelta_add
    (left : Matrix Output Route ℝ)
    (oldRouting freshRouting : Matrix Route Route ℝ)
    (right : Matrix Route Input ℝ) :
    routedDelta left (oldRouting + freshRouting) right =
      routedDelta left oldRouting right +
        routedDelta left freshRouting right := by
  simp [routedDelta, Matrix.mul_add, Matrix.add_mul]

/-! ## Source gradient decomposition -/

variable [Fintype Output] [Fintype Input]

/-- Gradient contribution to the left factor for one routing matrix.
The multiplication order is fixed by the matrix dimensions. -/
def leftFactorGradient
    (weightGradient : Matrix Output Input ℝ)
    (right : Matrix Route Input ℝ)
    (routing : Matrix Route Route ℝ) :
    Matrix Output Route ℝ :=
  (weightGradient * right.transpose) * routing.transpose

/-- Gradient contribution to the right factor for one routing matrix. -/
def rightFactorGradient
    (weightGradient : Matrix Output Input ℝ)
    (left : Matrix Output Route ℝ)
    (routing : Matrix Route Route ℝ) :
    Matrix Route Input ℝ :=
  routing.transpose * (left.transpose * weightGradient)

omit [Fintype Output] in
/-- The left-factor gradient is the sum of its old and fresh routing
contributions. -/
theorem leftFactorGradient_add
    (weightGradient : Matrix Output Input ℝ)
    (right : Matrix Route Input ℝ)
    (oldRouting freshRouting : Matrix Route Route ℝ) :
    leftFactorGradient weightGradient right (oldRouting + freshRouting) =
      leftFactorGradient weightGradient right oldRouting +
        leftFactorGradient weightGradient right freshRouting := by
  simp [leftFactorGradient, Matrix.mul_add]

omit [Fintype Input] in
/-- The right-factor gradient is the sum of its old and fresh routing
contributions. -/
theorem rightFactorGradient_add
    (weightGradient : Matrix Output Input ℝ)
    (left : Matrix Output Route ℝ)
    (oldRouting freshRouting : Matrix Route Route ℝ) :
    rightFactorGradient weightGradient left (oldRouting + freshRouting) =
      rightFactorGradient weightGradient left oldRouting +
        rightFactorGradient weightGradient left freshRouting := by
  simp [rightFactorGradient, Matrix.add_mul]

/-! ## Frobenius geometry -/

variable {Row Col : Type*} [Fintype Row] [Fintype Col]

/-- Entrywise pairing of two equally shaped real matrices. -/
def entrywisePairing
    (first second : Matrix Row Col ℝ) : ℝ :=
  ∑ row, ∑ col, first row col * second row col

/-- Squared Frobenius magnitude, kept algebraic for kernel-computable
fixtures. -/
def frobeniusSquared (matrix : Matrix Row Col ℝ) : ℝ :=
  entrywisePairing matrix matrix

theorem entrywisePairing_comm
    (first second : Matrix Row Col ℝ) :
    entrywisePairing first second =
      entrywisePairing second first := by
  simp only [entrywisePairing]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro col _
  ring

theorem entrywisePairing_add_left
    (first second third : Matrix Row Col ℝ) :
    entrywisePairing (first + second) third =
      entrywisePairing first third +
        entrywisePairing second third := by
  simp [entrywisePairing, Finset.sum_add_distrib, add_mul]

theorem entrywisePairing_add_right
    (first second third : Matrix Row Col ℝ) :
    entrywisePairing first (second + third) =
      entrywisePairing first second +
        entrywisePairing first third := by
  simp [entrywisePairing, Finset.sum_add_distrib, mul_add]

theorem frobeniusSquared_nonneg
    (matrix : Matrix Row Col ℝ) :
    0 ≤ frobeniusSquared matrix := by
  unfold frobeniusSquared entrywisePairing
  exact Finset.sum_nonneg fun row _ =>
    Finset.sum_nonneg fun col _ =>
      mul_self_nonneg (matrix row col)

/-- Zero squared Frobenius magnitude detects the zero matrix. -/
theorem frobeniusSquared_eq_zero_iff
    (matrix : Matrix Row Col ℝ) :
    frobeniusSquared matrix = 0 ↔ matrix = 0 := by
  constructor
  · intro zeroMagnitude
    ext row col
    have rowZero :
        ∑ col, matrix row col * matrix row col = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun row _ =>
          Finset.sum_nonneg fun col _ =>
            mul_self_nonneg (matrix row col))).mp
        zeroMagnitude row (Finset.mem_univ row)
    have entryZero : matrix row col * matrix row col = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun col _ => mul_self_nonneg (matrix row col))).mp
        rowZero col (Finset.mem_univ col)
    exact mul_self_eq_zero.mp entryZero
  · rintro rfl
    simp [frobeniusSquared, entrywisePairing]

/-- Exact polarization identity behind the source's gradient comparison. -/
theorem frobeniusSquared_add
    (oldContribution freshContribution : Matrix Row Col ℝ) :
    frobeniusSquared (oldContribution + freshContribution) =
      frobeniusSquared oldContribution +
        2 * entrywisePairing oldContribution freshContribution +
          frobeniusSquared freshContribution := by
  unfold frobeniusSquared
  rw [entrywisePairing_add_left, entrywisePairing_add_right,
    entrywisePairing_add_right,
    entrywisePairing_comm freshContribution oldContribution]
  ring

/-- Difference form of the polarization identity. -/
theorem frobeniusSquared_add_sub_fresh
    (oldContribution freshContribution : Matrix Row Col ℝ) :
    frobeniusSquared (oldContribution + freshContribution) -
        frobeniusSquared freshContribution =
      frobeniusSquared oldContribution +
        2 * entrywisePairing oldContribution freshContribution := by
  rw [frobeniusSquared_add]
  ring

/-- Exact sufficient condition for the source's strict gradient-magnitude
comparison.  It is stated at the actual gradient contributions, without
requiring a stronger routing-level surrogate. -/
theorem fresh_gradient_strictly_smaller
    (oldContribution freshContribution : Matrix Row Col ℝ)
    (oldNonzero : oldContribution ≠ 0)
    (nonnegativeAlignment :
      0 ≤ entrywisePairing oldContribution freshContribution) :
    frobeniusSquared freshContribution <
      frobeniusSquared (oldContribution + freshContribution) := by
  have oldMagnitudeNonzero :
      frobeniusSquared oldContribution ≠ 0 :=
    (frobeniusSquared_eq_zero_iff oldContribution).not.mpr oldNonzero
  have oldMagnitudePositive :
      0 < frobeniusSquared oldContribution :=
    lt_of_le_of_ne (frobeniusSquared_nonneg oldContribution)
      (Ne.symm oldMagnitudeNonzero)
  have identity :=
    frobeniusSquared_add_sub_fresh
      oldContribution freshContribution
  nlinarith

/-- At exact orthogonality, removing the old gradient path reduces squared
magnitude by exactly the old contribution's squared magnitude. -/
theorem orthogonal_gradient_exact_gap
    (oldContribution freshContribution : Matrix Row Col ℝ)
    (orthogonal :
      entrywisePairing oldContribution freshContribution = 0) :
    frobeniusSquared
          (oldContribution + freshContribution) -
        frobeniusSquared freshContribution =
      frobeniusSquared oldContribution := by
  rw [frobeniusSquared_add_sub_fresh, orthogonal]
  ring

/-- Source Theorem 3.1 for the left factor, under the exact alignment
condition on the induced old and fresh gradient contributions. -/
theorem leftFactor_fresh_gradient_strictly_smaller
    (weightGradient : Matrix Output Input ℝ)
    (right : Matrix Route Input ℝ)
    (oldRouting freshRouting : Matrix Route Route ℝ)
    (oldNonzero :
      leftFactorGradient weightGradient right oldRouting ≠ 0)
    (nonnegativeAlignment :
      0 ≤ entrywisePairing
        (leftFactorGradient weightGradient right oldRouting)
        (leftFactorGradient weightGradient right freshRouting)) :
    frobeniusSquared
        (leftFactorGradient weightGradient right freshRouting) <
      frobeniusSquared
        (leftFactorGradient weightGradient right
          (oldRouting + freshRouting)) := by
  rw [leftFactorGradient_add]
  exact fresh_gradient_strictly_smaller _ _
    oldNonzero nonnegativeAlignment

/-- Source Theorem 3.1 for the right factor, under the exact alignment
condition on the induced old and fresh gradient contributions. -/
theorem rightFactor_fresh_gradient_strictly_smaller
    (weightGradient : Matrix Output Input ℝ)
    (left : Matrix Output Route ℝ)
    (oldRouting freshRouting : Matrix Route Route ℝ)
    (oldNonzero :
      rightFactorGradient weightGradient left oldRouting ≠ 0)
    (nonnegativeAlignment :
      0 ≤ entrywisePairing
        (rightFactorGradient weightGradient left oldRouting)
        (rightFactorGradient weightGradient left freshRouting)) :
    frobeniusSquared
        (rightFactorGradient weightGradient left freshRouting) <
      frobeniusSquared
        (rightFactorGradient weightGradient left
          (oldRouting + freshRouting)) := by
  rw [rightFactorGradient_add]
  exact fresh_gradient_strictly_smaller _ _
    oldNonzero nonnegativeAlignment

/-! ## Orthogonality regularization -/

/-- Source Equation (26): squared Frobenius magnitude of the fresh route's
projection onto the declared old basis. -/
def routingOrthogonalityPenalty
    (oldBasis freshRouting : Matrix Route Route ℝ) : ℝ :=
  frobeniusSquared (oldBasis.transpose * freshRouting)

theorem routingOrthogonalityPenalty_nonneg
    (oldBasis freshRouting : Matrix Route Route ℝ) :
    0 ≤ routingOrthogonalityPenalty oldBasis freshRouting :=
  frobeniusSquared_nonneg _

/-- The penalty vanishes exactly when the advertised annihilation equation
holds. -/
theorem routingOrthogonalityPenalty_eq_zero_iff
    (oldBasis freshRouting : Matrix Route Route ℝ) :
    routingOrthogonalityPenalty oldBasis freshRouting = 0 ↔
      oldBasis.transpose * freshRouting = 0 := by
  exact frobeniusSquared_eq_zero_iff _

/-! ## Positive and negative fixtures -/

/-- Two disjoint routing axes have zero orthogonality penalty. -/
theorem disjoint_axis_penalty_zero :
    let oldBasis : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let freshRouting : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
    routingOrthogonalityPenalty oldBasis freshRouting = 0 := by
  norm_num [routingOrthogonalityPenalty, frobeniusSquared,
    entrywisePairing, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two]

/-- Reusing the same routing axis has positive unit penalty. -/
theorem overlapping_axis_penalty_positive :
    let route : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    routingOrthogonalityPenalty route route = 1 := by
  norm_num [routingOrthogonalityPenalty, frobeniusSquared,
    entrywisePairing, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two]

/-- Without nonnegative alignment, the source's strict comparison can
reverse completely: an anti-aligned fresh contribution cancels the full
gradient while the fresh-only gradient remains nonzero. -/
theorem antiAligned_gradient_reverses_comparison
    (oldContribution : Matrix Row Col ℝ)
    (oldNonzero : oldContribution ≠ 0) :
    frobeniusSquared
        (oldContribution + (-oldContribution)) <
      frobeniusSquared (-oldContribution) := by
  simp only [add_neg_cancel, frobeniusSquared]
  have positive :
      0 < entrywisePairing oldContribution oldContribution := by
    have nonzero :
        frobeniusSquared oldContribution ≠ 0 :=
      (frobeniusSquared_eq_zero_iff oldContribution).not.mpr
        oldNonzero
    exact lt_of_le_of_ne (frobeniusSquared_nonneg oldContribution)
      (Ne.symm nonzero)
  simpa [entrywisePairing] using positive

/-- A smaller update can increase an old loss more than a larger update.
Thus a gradient-magnitude comparison alone is not a finite-forgetting
theorem. -/
theorem smaller_update_norm_can_forget_more :
    let oldLoss : ℝ → ℝ := fun parameter => (parameter - 1) ^ 2
    ‖(-1 : ℝ)‖ < ‖(2 : ℝ)‖ ∧
      LowRankForgettingGeometry.finiteForgetting
          oldLoss 0 (-1) >
        LowRankForgettingGeometry.finiteForgetting oldLoss 0 2 := by
  norm_num [LowRankForgettingGeometry.finiteForgetting,
    Real.norm_eq_abs]

#print axioms blockDiagonalRouting_recovers_mixture
#print axioms routedDelta_add
#print axioms leftFactorGradient_add
#print axioms rightFactorGradient_add
#print axioms frobeniusSquared_eq_zero_iff
#print axioms frobeniusSquared_add_sub_fresh
#print axioms fresh_gradient_strictly_smaller
#print axioms leftFactor_fresh_gradient_strictly_smaller
#print axioms rightFactor_fresh_gradient_strictly_smaller
#print axioms routingOrthogonalityPenalty_eq_zero_iff
#print axioms antiAligned_gradient_reverses_comparison
#print axioms smaller_update_norm_can_forget_more

end

end ContinualLowRankRouting

end Mettapedia.MachineLearning.ContinualLearning
