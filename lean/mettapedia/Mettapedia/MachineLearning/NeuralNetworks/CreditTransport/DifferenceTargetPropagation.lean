import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.TargetPerturbation

/-!
# Difference target propagation

Lee, Zhang, Fischer, and Bengio, *Difference Target Propagation*
(arXiv:1412.7525), introduce the corrected lower-layer target

`base + feedback target - feedback current`

in Equation (15).  The correction enforces their stability condition (16)
exactly.  Theorem 2 then gives a local output-error improvement when the
linearized forward-after-feedback error is contractive.

This file recovers the exact affine theorem in arbitrary real normed spaces and
separates the nonlinear extension into a contractive linear term plus an
observable linearization remainder.  The latter is directly suitable for a
finite replay certificate.  Fixtures show a strict nontrivial improvement,
the fixed-point failure of the uncorrected target, and the loss of strictness at
contraction factor one.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace DifferenceTargetPropagation

variable {State : Type*}
  [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Equation (15): correct an inverse target by subtracting the feedback
model's value at the current upper-layer state. -/
def differenceTarget
    (feedback : State → State) (base current target : State) : State :=
  base + feedback target - feedback current

/-- The affine forward model based at a lower-layer state and its current
upper-layer image. -/
def affineForwardAt
    (linear : State →ₗ[ℝ] State)
    (base current point : State) : State :=
  current + linear (point - base)

/-- A norm formulation of the source's spectral contraction condition for
`I - forward ∘ feedback`. -/
def HasDifferenceContraction
    (forward feedback : State →ₗ[ℝ] State) (ratio : ℝ) : Prop :=
  0 ≤ ratio ∧
    ∀ delta,
      ‖delta - forward (feedback delta)‖ ≤ ratio * ‖delta‖

omit [NormedSpace ℝ State] in
/-- Difference correction enforces the source stability condition (16) for
every feedback function, without any inverse assumption. -/
@[simp] theorem differenceTarget_eq_base_of_target_eq_current
    (feedback : State → State) (base current : State) :
    differenceTarget feedback base current current = base := by
  simp [differenceTarget]

omit [NormedSpace ℝ State] in
/-- Equation (18): the corrected lower-layer displacement is exactly the
difference of the two feedback values. -/
theorem differenceTarget_sub_base
    (feedback : State → State) (base current target : State) :
    differenceTarget feedback base current target - base =
      feedback target - feedback current := by
  unfold differenceTarget
  abel

/-- For a linear feedback model, the corrected displacement is the feedback
image of the upper-layer target displacement. -/
theorem linear_differenceTarget_sub_base
    (feedback : State →ₗ[ℝ] State)
    (base current target : State) :
    differenceTarget feedback base current target - base =
      feedback (target - current) := by
  rw [differenceTarget_sub_base, map_sub]

/-- Exact affine core of the source's Theorem 2.  After the corrected lower
target is reached, the remaining upper-layer error is
`(I - forward ∘ feedback)` applied to the old error. -/
theorem affine_difference_output_error
    (forward feedback : State →ₗ[ℝ] State)
    (base current target : State) :
    target -
        affineForwardAt forward base current
          (differenceTarget feedback base current target) =
      (target - current) -
        forward (feedback (target - current)) := by
  rw [affineForwardAt, linear_differenceTarget_sub_base]
  abel

/-- A contraction factor strictly below one makes the affine corrected target
strictly reduce every nonzero output error. -/
theorem affine_differenceTarget_strictly_improves
    (forward feedback : State →ₗ[ℝ] State)
    (base current target : State) (ratio : ℝ)
    (contract :
      HasDifferenceContraction forward feedback ratio)
    (hratioLt : ratio < 1) (htarget : target ≠ current) :
    ‖target -
        affineForwardAt forward base current
          (differenceTarget feedback base current target)‖ <
      ‖target - current‖ := by
  rw [affine_difference_output_error]
  have hbound := contract.2 (target - current)
  have hnormPositive : 0 < ‖target - current‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr htarget)
  exact lt_of_le_of_lt hbound
    (mul_lt_of_lt_one_left hnormPositive hratioLt)

/-- Squared-error presentation matching Equation (19) in the source. -/
theorem affine_differenceTarget_sq_strictly_improves
    (forward feedback : State →ₗ[ℝ] State)
    (base current target : State) (ratio : ℝ)
    (contract :
      HasDifferenceContraction forward feedback ratio)
    (hratioLt : ratio < 1) (htarget : target ≠ current) :
    ‖target -
        affineForwardAt forward base current
          (differenceTarget feedback base current target)‖ ^ 2 <
      ‖target - current‖ ^ 2 := by
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).2
  exact
    affine_differenceTarget_strictly_improves
      forward feedback base current target ratio contract hratioLt htarget

/-! ## Nonlinear forward map with an explicit remainder -/

/-- A nonlinear forward map inherits the affine contraction bound up to its
measured linearization remainder at the proposed corrected target. -/
theorem nonlinear_difference_output_error_le
    (forward : State → State)
    (linear feedback : State →ₗ[ℝ] State)
    (base current target : State) (ratio remainder : ℝ)
    (contract :
      HasDifferenceContraction linear feedback ratio)
    (hlinearization :
      ‖(forward (differenceTarget feedback base current target) - current) -
          linear (feedback (target - current))‖ ≤ remainder) :
    ‖target -
        forward (differenceTarget feedback base current target)‖ ≤
      ratio * ‖target - current‖ + remainder := by
  let delta := target - current
  let residual :=
    (forward (differenceTarget feedback base current target) - current) -
      linear (feedback delta)
  have hdecompose :
      target - forward (differenceTarget feedback base current target) =
        (delta - linear (feedback delta)) - residual := by
    dsimp [delta, residual]
    abel
  rw [hdecompose]
  calc
    ‖(delta - linear (feedback delta)) - residual‖ ≤
        ‖delta - linear (feedback delta)‖ + ‖residual‖ :=
      norm_sub_le _ _
    _ ≤ ratio * ‖target - current‖ + remainder :=
      add_le_add (contract.2 (target - current)) hlinearization

/-- The nonlinear replay is certified to improve whenever the contraction
term plus the measured remainder fits strictly inside the old error. -/
theorem nonlinear_differenceTarget_strictly_improves
    (forward : State → State)
    (linear feedback : State →ₗ[ℝ] State)
    (base current target : State) (ratio remainder : ℝ)
    (contract :
      HasDifferenceContraction linear feedback ratio)
    (hlinearization :
      ‖(forward (differenceTarget feedback base current target) - current) -
          linear (feedback (target - current))‖ ≤ remainder)
    (hbudget :
      ratio * ‖target - current‖ + remainder <
        ‖target - current‖) :
    ‖target -
        forward (differenceTarget feedback base current target)‖ <
      ‖target - current‖ :=
  lt_of_le_of_lt
    (nonlinear_difference_output_error_le
      forward linear feedback base current target ratio remainder
      contract hlinearization)
    hbudget

/-! ## Scalar executable fixtures -/

/-- Scalar multiplication as a real linear map. -/
def scalarLinear (scale : ℝ) : ℝ →ₗ[ℝ] ℝ where
  toFun value := scale * value
  map_add' left right := by ring
  map_smul' scalar value := by
    simp
    ring

@[simp] theorem scalarLinear_apply (scale value : ℝ) :
    scalarLinear scale value = scale * value :=
  rfl

/-- A half-scale feedback model produces a strict, nonzero improvement in the
affine fixture. -/
theorem scalar_half_feedback_strictly_improves :
    let forward := scalarLinear 1
    let feedback := scalarLinear (1 / 2)
    let lower := differenceTarget feedback 2 3 5
    lower = 3 ∧
      affineForwardAt forward 2 3 lower = 4 ∧
      ‖(5 : ℝ) - affineForwardAt forward 2 3 lower‖ <
        ‖(5 : ℝ) - 3‖ := by
  norm_num [differenceTarget, affineForwardAt, scalarLinear]

/-- An uncorrected inverse target can move the lower state even when upper
target and current state agree; difference correction restores the fixed
point exactly. -/
theorem vanillaFeedback_ne_and_differenceTarget_eq :
    let feedback := fun value : ℝ => 2 * value
    feedback 1 = 2 ∧
      differenceTarget feedback 1 1 1 = 1 := by
  norm_num [differenceTarget]

/-- At contraction factor one, the corrected target need not strictly reduce
the output error. -/
theorem unit_ratio_does_not_strictly_improve :
    let forward := scalarLinear 0
    let feedback := scalarLinear 0
    let lower := differenceTarget feedback 0 0 1
    ‖(1 : ℝ) - affineForwardAt forward 0 0 lower‖ =
      ‖(1 : ℝ) - 0‖ := by
  norm_num [differenceTarget, affineForwardAt, scalarLinear,
    Real.norm_eq_abs]

#print axioms differenceTarget_eq_base_of_target_eq_current
#print axioms affine_difference_output_error
#print axioms affine_differenceTarget_sq_strictly_improves
#print axioms nonlinear_difference_output_error_le
#print axioms nonlinear_differenceTarget_strictly_improves
#print axioms scalar_half_feedback_strictly_improves
#print axioms vanillaFeedback_ne_and_differenceTarget_eq
#print axioms unit_ratio_does_not_strictly_improve

end DifferenceTargetPropagation

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
