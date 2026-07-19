import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.TrustRegion

/-!
# Plain and residual depth recurrences

A plain linear chain multiplies by each block factor.  A residual chain
multiplies by one plus that factor.  This elementary distinction prevents the
Depth-μP cancellation theorem for a plain block from being transferred to a
residual stack.

The requested deterministic, depth-uniform order-one bound under the aligned
Depth-μP residual factor `1 / sqrt(depth)` is false: along square depths the
stack is at least linear in the square root of depth.  We prove that
counterexample rather than importing an infinite-width probability claim.
For comparison, the stronger deterministic scaling `1 / depth` has the
uniform bound `exp 1`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Plain versus residual recurrence -/

/-- End-to-end scalar multiplier of a plain depth stack. -/
noncomputable def plainStackMultiplier (blockMultiplier : ℝ) (depth : ℕ) : ℝ :=
  blockMultiplier ^ depth

/-- End-to-end scalar multiplier of an aligned residual depth stack. -/
noncomputable def residualStackMultiplier
    (blockMultiplier : ℝ) (depth : ℕ) : ℝ :=
  (1 + blockMultiplier) ^ depth

theorem plainStackMultiplier_succ
    (blockMultiplier : ℝ) (depth : ℕ) :
    plainStackMultiplier blockMultiplier (depth + 1) =
      plainStackMultiplier blockMultiplier depth * blockMultiplier := by
  simp [plainStackMultiplier, pow_succ]

theorem residualStackMultiplier_succ
    (blockMultiplier : ℝ) (depth : ℕ) :
    residualStackMultiplier blockMultiplier (depth + 1) =
      residualStackMultiplier blockMultiplier depth *
        (1 + blockMultiplier) := by
  simp [residualStackMultiplier, pow_succ]

/-- Positive contrast: a zero plain block kills every positive-depth signal,
whereas a zero residual branch leaves the identity path intact. -/
theorem zeroBlock_plain_vs_residual (depth : ℕ) (hdepth : 0 < depth) :
    plainStackMultiplier 0 depth = 0 ∧
      residualStackMultiplier 0 depth = 1 := by
  constructor
  · simp [plainStackMultiplier, Nat.ne_of_gt hdepth]
  · simp [residualStackMultiplier]

/-- The plain block's optimizer-scale cancellation does not extend through a
residual skip: the effective factor is the positive Adam scale plus one. -/
theorem depthMuP_residual_factor_eq_scale_add_one
    (width depth : ℕ) (hwidth : 0 < width) (hdepth : 0 < depth) :
    depthMuPAdamLearningRateScale width depth *
        (1 + depthMuPHiddenMultiplier width depth) =
      depthMuPAdamLearningRateScale width depth + 1 := by
  rw [mul_add, mul_one,
    depthMuPAdamScale_mul_hiddenMultiplier width depth hwidth hdepth]

/-- Consequently the residual factor is strictly larger than one. -/
theorem depthMuP_residual_factor_gt_one
    (width depth : ℕ) (hwidth : 0 < width) (hdepth : 0 < depth) :
    1 < depthMuPAdamLearningRateScale width depth *
      (1 + depthMuPHiddenMultiplier width depth) := by
  rw [depthMuP_residual_factor_eq_scale_add_one width depth hwidth hdepth]
  have hscale : 0 < depthMuPAdamLearningRateScale width depth := by
    unfold depthMuPAdamLearningRateScale
    apply Real.sqrt_pos.2
    positivity
  linarith

/-- Explicit negation of the invalid universal transfer from the plain-chain
cancellation theorem to residual blocks.  The unit-width, unit-depth residual
block already has effective factor strictly greater than one. -/
theorem depthMuP_residual_cancellation_not_universal :
    ¬ ∀ width depth : ℕ, 0 < width → 0 < depth →
      depthMuPAdamLearningRateScale width depth *
        (1 + depthMuPHiddenMultiplier width depth) = 1 := by
  intro huniversal
  have heq := huniversal 1 1 (by norm_num) (by norm_num)
  have hgt := depthMuP_residual_factor_gt_one 1 1 (by norm_num) (by norm_num)
  linarith

/-! ## Failure of the requested `1/sqrt(depth)` uniform bound -/

/-- Aligned residual stack using the Depth-μP depth factor at unit width. -/
noncomputable def alignedDepthMuPResidualStack (depth : ℕ) : ℝ :=
  (1 + 1 / Real.sqrt (depth : ℝ)) ^ depth

/-- Along square depths, Bernoulli's inequality gives a linear lower bound in
the square root of depth. -/
theorem alignedDepthMuPResidualStack_square_lower_bound
    (root : ℕ) (hroot : 0 < root) :
    (root : ℝ) + 1 ≤ alignedDepthMuPResidualStack (root ^ 2) := by
  have hsqrt : Real.sqrt (((root ^ 2 : ℕ) : ℝ)) = (root : ℝ) := by
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg root)]
  have hneg : (-2 : ℝ) ≤ 0 := by norm_num
  have hinv : 0 ≤ (root : ℝ)⁻¹ := by positivity
  have hinvLower : (-2 : ℝ) ≤ (root : ℝ)⁻¹ := hneg.trans hinv
  have hbern := one_add_mul_le_pow
    (a := ((root : ℝ)⁻¹)) (n := root ^ 2) hinvLower
  rw [alignedDepthMuPResidualStack, hsqrt, one_div]
  calc
    (root : ℝ) + 1 = 1 + ((root ^ 2 : ℕ) : ℝ) * (root : ℝ)⁻¹ := by
      rw [Nat.cast_pow]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hroot)]
      ring
    _ ≤ (1 + (root : ℝ)⁻¹) ^ (root ^ 2) := hbern

/-- Deterministic counterexample to any finite, depth-uniform upper bound for
the aligned `1/sqrt(depth)` residual stack. -/
theorem alignedDepthMuPResidualStack_unbounded
    (bound : ℝ) :
    ∃ depth : ℕ, 0 < depth ∧
      bound < alignedDepthMuPResidualStack depth := by
  obtain ⟨root, hrootBound⟩ :
      ∃ root : ℕ, max bound 0 < root := exists_nat_gt (max bound 0)
  have hroot : 0 < root := by
    exact_mod_cast (lt_of_le_of_lt (le_max_right bound 0) hrootBound)
  refine ⟨root ^ 2, pow_pos hroot 2, ?_⟩
  have hlower := alignedDepthMuPResidualStack_square_lower_bound root hroot
  have hboundRoot : bound < (root : ℝ) :=
    lt_of_le_of_lt (le_max_left bound 0) hrootBound
  linarith

/-- Therefore the proposed deterministic uniform order-one theorem is false. -/
theorem no_uniform_bound_for_alignedDepthMuPResidualStack :
    ¬ ∃ bound : ℝ, ∀ depth : ℕ, 0 < depth →
      alignedDepthMuPResidualStack depth ≤ bound := by
  rintro ⟨bound, hbound⟩
  obtain ⟨depth, hdepth, hexceeds⟩ :=
    alignedDepthMuPResidualStack_unbounded bound
  exact (not_lt_of_ge (hbound depth hdepth)) hexceeds

/-- Concrete negative fixture: the aligned Depth-μP residual multiplier at
depth four is already `81/16`, not order one by exact cancellation. -/
theorem alignedDepthMuPResidualStack_depthFour :
    alignedDepthMuPResidualStack 4 = 81 / 16 := by
  norm_num [alignedDepthMuPResidualStack]

/-! ## A sufficient deterministic alternative -/

/-- Residual stack with the stronger block factor `1 / depth`. -/
noncomputable def inverseDepthResidualStack (depth : ℕ) : ℝ :=
  (1 + (depth : ℝ)⁻¹) ^ depth

/-- Unlike the aligned Depth-μP factor, `1 / depth` has a depth-uniform exact
real upper bound. -/
theorem inverseDepthResidualStack_le_exp_one (depth : ℕ) :
    inverseDepthResidualStack depth ≤ Real.exp 1 := by
  exact Real.one_add_inv_pow_le_exp

/-- Positive fixture at depth four. -/
theorem inverseDepthResidualStack_depthFour :
    inverseDepthResidualStack 4 = 625 / 256 := by
  norm_num [inverseDepthResidualStack]

inductive ResidualScalingClaimStatus
  | deterministicTheorem
  | infiniteWidthReproductionTarget
  deriving DecidableEq, Repr

structure ResidualScalingBoundaryClaim where
  description : String
  status : ResidualScalingClaimStatus
  deriving DecidableEq, Repr

/-- The scalar finite-depth random moment theorem is provided in
`ResidualMomentBound`; noncommutative matrix and infinite-width extensions
remain reproduction targets. -/
def residualInfiniteWidthBoundary : ResidualScalingBoundaryClaim where
  description := "matrix random residual cancellation in the infinite-width limit"
  status := .infiniteWidthReproductionTarget

theorem residualInfiniteWidthBoundary_not_deterministic :
    residualInfiniteWidthBoundary.status ≠ .deterministicTheorem := by
  decide

#print axioms no_uniform_bound_for_alignedDepthMuPResidualStack
#print axioms depthMuP_residual_cancellation_not_universal
#print axioms inverseDepthResidualStack_le_exp_one

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
