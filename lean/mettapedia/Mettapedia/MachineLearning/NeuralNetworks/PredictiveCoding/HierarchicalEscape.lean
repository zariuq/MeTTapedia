import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LocalPreconditionedRate
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Honest hierarchical residuals and the multigrid boundary

This file tests the proposed hierarchical escape at its smallest dyadic
cell.  A coarse latent predicts two fine children through ordinary squared
residuals, while the children retain their original fine-level residuals.
The settling vector field is defined from derivatives of that augmented
energy, not postulated as a multigrid operator.

The result is a precise obstruction: except when the two fine targets agree,
the added hierarchical residuals move the original fine optimum.  A
multigrid coarse correction must preserve that optimum.  Thus the honest
predictive-coding hierarchy specified here is a different objective, not a
two-grid solver for the original one.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-- Fine children and their shared coarse predictor in one dyadic cell. -/
@[ext] structure DyadicCellState where
  left : ℝ
  right : ℝ
  coarse : ℝ

instance : Zero DyadicCellState := ⟨⟨0, 0, 0⟩⟩

@[simp] theorem DyadicCellState.zero_left : (0 : DyadicCellState).left = 0 := rfl
@[simp] theorem DyadicCellState.zero_right : (0 : DyadicCellState).right = 0 := rfl
@[simp] theorem DyadicCellState.zero_coarse : (0 : DyadicCellState).coarse = 0 := rfl

/-- Original fine-level quadratic objective for two independently targeted
children. -/
def dyadicFineEnergy (targetLeft targetRight left right : ℝ) : ℝ :=
  (left - targetLeft) ^ 2 + (right - targetRight) ^ 2

/-- Honest two-level PC energy: retain the fine residuals and add one
prediction residual from the coarse latent to each child. -/
def dyadicHierarchicalEnergy (targetLeft targetRight : ℝ)
    (state : DyadicCellState) : ℝ :=
  dyadicFineEnergy targetLeft targetRight state.left state.right +
    (state.left - state.coarse) ^ 2 +
    (state.right - state.coarse) ^ 2

theorem dyadicHierarchicalEnergy_hasDerivAt_left
    (targetLeft targetRight : ℝ) (state : DyadicCellState) :
    HasDerivAt
      (fun left => dyadicHierarchicalEnergy targetLeft targetRight
        { state with left := left })
      (4 * state.left - 2 * targetLeft - 2 * state.coarse) state.left := by
  unfold dyadicHierarchicalEnergy dyadicFineEnergy
  convert (((((hasDerivAt_id' (𝕜 := ℝ) state.left).sub
      (hasDerivAt_const state.left targetLeft)).pow 2).add
    (((hasDerivAt_const state.left state.right).sub
      (hasDerivAt_const state.left targetRight)).pow 2)).add
    (((hasDerivAt_id' (𝕜 := ℝ) state.left).sub
      (hasDerivAt_const state.left state.coarse)).pow 2)).add
    (((hasDerivAt_const state.left state.right).sub
      (hasDerivAt_const state.left state.coarse)).pow 2) using 1
  all_goals
    try rfl
    try simp only [Pi.sub_apply]
    try ring

theorem dyadicHierarchicalEnergy_hasDerivAt_right
    (targetLeft targetRight : ℝ) (state : DyadicCellState) :
    HasDerivAt
      (fun right => dyadicHierarchicalEnergy targetLeft targetRight
        { state with right := right })
      (4 * state.right - 2 * targetRight - 2 * state.coarse) state.right := by
  unfold dyadicHierarchicalEnergy dyadicFineEnergy
  convert (((((hasDerivAt_const state.right state.left).sub
      (hasDerivAt_const state.right targetLeft)).pow 2).add
    (((hasDerivAt_id' (𝕜 := ℝ) state.right).sub
      (hasDerivAt_const state.right targetRight)).pow 2)).add
    (((hasDerivAt_const state.right state.left).sub
      (hasDerivAt_const state.right state.coarse)).pow 2)).add
    (((hasDerivAt_id' (𝕜 := ℝ) state.right).sub
      (hasDerivAt_const state.right state.coarse)).pow 2) using 1
  all_goals
    try rfl
    try simp only [Pi.sub_apply]
    try ring

theorem dyadicHierarchicalEnergy_hasDerivAt_coarse
    (targetLeft targetRight : ℝ) (state : DyadicCellState) :
    HasDerivAt
      (fun coarse => dyadicHierarchicalEnergy targetLeft targetRight
        { state with coarse := coarse })
      (4 * state.coarse - 2 * state.left - 2 * state.right) state.coarse := by
  unfold dyadicHierarchicalEnergy dyadicFineEnergy
  convert (((((hasDerivAt_const state.coarse state.left).sub
      (hasDerivAt_const state.coarse targetLeft)).pow 2).add
    (((hasDerivAt_const state.coarse state.right).sub
      (hasDerivAt_const state.coarse targetRight)).pow 2)).add
    (((hasDerivAt_const state.coarse state.left).sub
      (hasDerivAt_id' (𝕜 := ℝ) state.coarse)).pow 2)).add
    (((hasDerivAt_const state.coarse state.right).sub
      (hasDerivAt_id' (𝕜 := ℝ) state.coarse)).pow 2) using 1
  all_goals
    try rfl
    try simp only [Pi.sub_apply]
    try ring

/-- Gradient read directly from the three partial derivatives of the honest
augmented energy. -/
noncomputable def dyadicHierarchicalGradient
    (targetLeft targetRight : ℝ) (state : DyadicCellState) : DyadicCellState where
  left := deriv
    (fun left => dyadicHierarchicalEnergy targetLeft targetRight
      { state with left := left }) state.left
  right := deriv
    (fun right => dyadicHierarchicalEnergy targetLeft targetRight
      { state with right := right }) state.right
  coarse := deriv
    (fun coarse => dyadicHierarchicalEnergy targetLeft targetRight
      { state with coarse := coarse }) state.coarse

theorem dyadicHierarchicalGradient_eq
    (targetLeft targetRight : ℝ) (state : DyadicCellState) :
    dyadicHierarchicalGradient targetLeft targetRight state =
      { left := 4 * state.left - 2 * targetLeft - 2 * state.coarse
        right := 4 * state.right - 2 * targetRight - 2 * state.coarse
        coarse := 4 * state.coarse - 2 * state.left - 2 * state.right } := by
  ext <;>
    simp [dyadicHierarchicalGradient,
      (dyadicHierarchicalEnergy_hasDerivAt_left targetLeft targetRight state).deriv,
      (dyadicHierarchicalEnergy_hasDerivAt_right targetLeft targetRight state).deriv,
      (dyadicHierarchicalEnergy_hasDerivAt_coarse targetLeft targetRight state).deriv]

/-- Gradient-descent settling step derived from the augmented energy. -/
noncomputable def dyadicHierarchicalSettlingStep (stepSize : ℝ)
    (targetLeft targetRight : ℝ) (state : DyadicCellState) : DyadicCellState where
  left := state.left - stepSize *
    (dyadicHierarchicalGradient targetLeft targetRight state).left
  right := state.right - stepSize *
    (dyadicHierarchicalGradient targetLeft targetRight state).right
  coarse := state.coarse - stepSize *
    (dyadicHierarchicalGradient targetLeft targetRight state).coarse

theorem dyadicHierarchicalSettlingStep_eq
    (stepSize targetLeft targetRight : ℝ) (state : DyadicCellState) :
    dyadicHierarchicalSettlingStep stepSize targetLeft targetRight state =
      { left := state.left - stepSize *
          (4 * state.left - 2 * targetLeft - 2 * state.coarse)
        right := state.right - stepSize *
          (4 * state.right - 2 * targetRight - 2 * state.coarse)
        coarse := state.coarse - stepSize *
          (4 * state.coarse - 2 * state.left - 2 * state.right) } := by
  rw [dyadicHierarchicalSettlingStep, dyadicHierarchicalGradient_eq]

/-- With a nonzero step size, a state is fixed by the derived settling
update exactly when it is stationary for the augmented energy. -/
theorem dyadicHierarchicalSettlingStep_eq_self_iff
    (stepSize targetLeft targetRight : ℝ) (state : DyadicCellState)
    (hstep : stepSize ≠ 0) :
    dyadicHierarchicalSettlingStep stepSize targetLeft targetRight state = state ↔
      dyadicHierarchicalGradient targetLeft targetRight state = 0 := by
  constructor
  · intro h
    have hleft := congrArg DyadicCellState.left h
    have hright := congrArg DyadicCellState.right h
    have hcoarse := congrArg DyadicCellState.coarse h
    ext
    · simp only [dyadicHierarchicalSettlingStep] at hleft
      simp only [DyadicCellState.zero_left]
      have hmul : stepSize *
          (dyadicHierarchicalGradient targetLeft targetRight state).left = 0 := by
        linarith
      exact (mul_eq_zero.mp hmul).resolve_left hstep
    · simp only [dyadicHierarchicalSettlingStep] at hright
      simp only [DyadicCellState.zero_right]
      have hmul : stepSize *
          (dyadicHierarchicalGradient targetLeft targetRight state).right = 0 := by
        linarith
      exact (mul_eq_zero.mp hmul).resolve_left hstep
    · simp only [dyadicHierarchicalSettlingStep] at hcoarse
      simp only [DyadicCellState.zero_coarse]
      have hmul : stepSize *
          (dyadicHierarchicalGradient targetLeft targetRight state).coarse = 0 := by
        linarith
      exact (mul_eq_zero.mp hmul).resolve_left hstep
  · intro h
    have hleft := congrArg DyadicCellState.left h
    have hright := congrArg DyadicCellState.right h
    have hcoarse := congrArg DyadicCellState.coarse h
    ext
    · simp only [dyadicHierarchicalSettlingStep]
      simp at hleft
      rw [hleft, mul_zero, sub_zero]
    · simp only [dyadicHierarchicalSettlingStep]
      simp at hright
      rw [hright, mul_zero, sub_zero]
    · simp only [dyadicHierarchicalSettlingStep]
      simp at hcoarse
      rw [hcoarse, mul_zero, sub_zero]

/-- The unique stationary point computed from the derived gradient. -/
noncomputable def dyadicHierarchicalStationaryState
    (targetLeft targetRight : ℝ) : DyadicCellState where
  left := (3 * targetLeft + targetRight) / 4
  right := (targetLeft + 3 * targetRight) / 4
  coarse := (targetLeft + targetRight) / 2

theorem dyadicHierarchicalGradient_eq_zero_iff
    (targetLeft targetRight : ℝ) (state : DyadicCellState) :
    dyadicHierarchicalGradient targetLeft targetRight state = 0 ↔
      state = dyadicHierarchicalStationaryState targetLeft targetRight := by
  rw [dyadicHierarchicalGradient_eq]
  constructor
  · intro h
    have hleft := congrArg DyadicCellState.left h
    have hright := congrArg DyadicCellState.right h
    have hcoarse := congrArg DyadicCellState.coarse h
    simp at hleft hright hcoarse
    ext <;> simp [dyadicHierarchicalStationaryState] <;> linarith
  · intro h
    subst state
    ext <;> simp [dyadicHierarchicalStationaryState] <;> ring

/-- Positive fixture: if the siblings agree, adding their shared predictor
preserves the original fine optimum. -/
theorem dyadicHierarchy_preserves_equal_targets (target : ℝ) :
    dyadicHierarchicalGradient target target
      { left := target, right := target, coarse := target } = 0 := by
  rw [dyadicHierarchicalGradient_eq]
  ext <;> simp <;> ring

/-- L3 obstruction crown: the honest residual hierarchy preserves the
original two-child fine optimum for some coarse value if and only if the two
fine targets agree.  Generic fine states therefore cannot share the original
fixed point with this augmented objective. -/
theorem dyadicHierarchy_preserves_fine_optimum_iff
    (targetLeft targetRight : ℝ) :
    (∃ coarse,
      dyadicHierarchicalGradient targetLeft targetRight
        { left := targetLeft, right := targetRight, coarse := coarse } = 0) ↔
      targetLeft = targetRight := by
  constructor
  · rintro ⟨coarse, h⟩
    rw [dyadicHierarchicalGradient_eq] at h
    have hleft := congrArg DyadicCellState.left h
    have hright := congrArg DyadicCellState.right h
    simp at hleft hright
    linarith
  · intro hequal
    subst targetRight
    exact ⟨targetLeft, dyadicHierarchy_preserves_equal_targets targetLeft⟩

/-- Dynamical form of the obstruction: for every nonzero step size, the
derived settling update fixes the original fine optimum for some coarse
state exactly when the two fine targets agree. -/
theorem dyadicHierarchy_settling_preserves_fine_optimum_iff
    (stepSize targetLeft targetRight : ℝ) (hstep : stepSize ≠ 0) :
    (∃ coarse,
      dyadicHierarchicalSettlingStep stepSize targetLeft targetRight
        { left := targetLeft, right := targetRight, coarse := coarse } =
      { left := targetLeft, right := targetRight, coarse := coarse }) ↔
      targetLeft = targetRight := by
  constructor
  · rintro ⟨coarse, hfixed⟩
    apply dyadicHierarchy_preserves_fine_optimum_iff targetLeft targetRight |>.mp
    exact ⟨coarse,
      (dyadicHierarchicalSettlingStep_eq_self_iff stepSize targetLeft targetRight
        { left := targetLeft, right := targetRight, coarse := coarse } hstep).mp hfixed⟩
  · intro hequal
    obtain ⟨coarse, hstationary⟩ :=
      (dyadicHierarchy_preserves_fine_optimum_iff targetLeft targetRight).mpr hequal
    exact ⟨coarse,
      (dyadicHierarchicalSettlingStep_eq_self_iff stepSize targetLeft targetRight
        { left := targetLeft, right := targetRight, coarse := coarse } hstep).mpr hstationary⟩

/-- Exact Galerkin correction in the constant coarse subspace: restrict the
fine residual by averaging, solve the scalar coarse problem, and prolong the
correction equally to both children. -/
noncomputable def dyadicGalerkinCoarseCorrection
    (targetLeft targetRight left right : ℝ) : ℝ × ℝ :=
  let meanError := ((left - targetLeft) + (right - targetRight)) / 2
  (left - meanError, right - meanError)

/-- Unlike the augmented residual hierarchy, an exact coarse correction
always preserves a solved fine problem. -/
theorem dyadicGalerkinCoarseCorrection_preserves_fine_optimum
    (targetLeft targetRight : ℝ) :
    dyadicGalerkinCoarseCorrection targetLeft targetRight targetLeft targetRight =
      (targetLeft, targetRight) := by
  ext <;> simp [dyadicGalerkinCoarseCorrection]

/-- Active fixture: a common-mode fine error is eliminated by the exact
coarse correction. -/
theorem dyadicGalerkinCoarseCorrection_removes_common_error :
    dyadicGalerkinCoarseCorrection 0 0 1 1 = (0, 0) := by
  norm_num [dyadicGalerkinCoarseCorrection]

/-- Mismatch fixture: at the opposite-target fine optimum, a quarter-step of
the honest hierarchical settling dynamics moves both children, whereas the
Galerkin correction above leaves every fine optimum fixed. -/
theorem dyadicHierarchy_oppositeTargets_settling_moves_fine_optimum :
    dyadicHierarchicalSettlingStep (1 / 4) 1 (-1)
      { left := 1, right := -1, coarse := 0 } =
      { left := 1 / 2, right := -1 / 2, coarse := 0 } := by
  rw [dyadicHierarchicalSettlingStep_eq]
  ext <;> norm_num

/-- Negative fixture: opposite fine targets are pulled halfway toward their
shared coarse predictor, so the augmented stationary point differs from the
original fine optimum. -/
theorem dyadicHierarchy_oppositeTargets_changes_fine_optimum :
    dyadicHierarchicalStationaryState 1 (-1) =
      { left := 1 / 2, right := -1 / 2, coarse := 0 } := by
  ext <;> norm_num [dyadicHierarchicalStationaryState]

#print axioms dyadicHierarchy_preserves_fine_optimum_iff
#print axioms dyadicHierarchy_settling_preserves_fine_optimum_iff

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
