import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AndersonGainGeometry

/-!
# One-mode central-flow projection geometry

Cohen, Damian, Talwalkar, and Kolter, *Understanding Optimization in Deep
Learning with Central Flows* (arXiv:2410.24206), equations (12)--(15), derive
a reduced flow for gradient descent at the edge of stability.  In the
one-unstable-mode regime, the oscillation variance is chosen to cancel the
sharpness drift.  Substitution turns the sharpness-penalized flow into the
negative loss gradient projected onto the orthogonal complement of the
sharpness gradient.

This file makes that reduced algebra exact.  It proves uniqueness of the
balancing variance, its sign boundary, the penalized-to-projected-flow
identity, exact sharpness preservation, and monotone loss descent.  The
projection is the same Hilbert-space residual already used by depth-one
Anderson acceleration, so the existing least-squares and norm identities are
reused rather than rederived.

The source explicitly describes its time-averaging and Taylor derivation as
informal.  Nothing here claims that a discrete neural-network training
trajectory satisfies that approximation, that the top eigenspace is
one-dimensional, or that the required progressive-sharpening regime holds.
The results are exact properties of the declared one-mode reduced flow.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CentralFlowProjection

open scoped InnerProductSpace

noncomputable section

/-! ## Scalar balance law -/

/-- Equation (12): sharpness drift under a learning-rate-scaled progressive
force and an oscillation-induced stabilizing force. -/
def sharpnessDrift
    (learningRate progressiveSharpening sharpnessGradientNormSq variance : ℝ) :
    ℝ :=
  learningRate *
    (progressiveSharpening - variance * sharpnessGradientNormSq / 2)

/-- Equation (13): the variance that balances progressive sharpening. -/
def balanceVariance
    (progressiveSharpening sharpnessGradientNormSq : ℝ) : ℝ :=
  2 * progressiveSharpening / sharpnessGradientNormSq

/-- With nonzero learning rate and sharpness gradient, the balancing variance
is the unique zero of the affine sharpness-drift law. -/
theorem sharpnessDrift_eq_zero_iff
    (learningRate progressiveSharpening sharpnessGradientNormSq variance : ℝ)
    (learningRate_ne_zero : learningRate ≠ 0)
    (sharpnessGradientNormSq_ne_zero : sharpnessGradientNormSq ≠ 0) :
    sharpnessDrift learningRate progressiveSharpening
        sharpnessGradientNormSq variance = 0 ↔
      variance =
        balanceVariance progressiveSharpening sharpnessGradientNormSq := by
  unfold sharpnessDrift balanceVariance
  constructor
  · intro driftZero
    have forceZero :
        progressiveSharpening -
            variance * sharpnessGradientNormSq / 2 = 0 := by
      exact (mul_eq_zero.mp driftZero).resolve_left learningRate_ne_zero
    field_simp [sharpnessGradientNormSq_ne_zero]
    nlinarith
  · intro varianceEq
    rw [varianceEq]
    field_simp [sharpnessGradientNormSq_ne_zero]
    ring

/-- The balancing variance is positive exactly in the progressive-sharpening
regime when the squared gradient norm is positive. -/
theorem balanceVariance_pos_iff
    (progressiveSharpening sharpnessGradientNormSq : ℝ)
    (sharpnessGradientNormSq_pos : 0 < sharpnessGradientNormSq) :
    0 <
        balanceVariance progressiveSharpening sharpnessGradientNormSq ↔
      0 < progressiveSharpening := by
  constructor
  · intro variancePos
    rcases div_pos_iff.mp variancePos with signs | signs
    · linarith [signs.1]
    · linarith [signs.2, sharpnessGradientNormSq_pos]
  · intro progressivePos
    exact div_pos (by positivity) sharpnessGradientNormSq_pos

/-- Outside progressive sharpening, equation (13) asks for a negative
variance and therefore cannot describe a physical oscillation covariance. -/
theorem balanceVariance_neg_of_regressive
    (progressiveSharpening sharpnessGradientNormSq : ℝ)
    (progressiveSharpening_neg : progressiveSharpening < 0)
    (sharpnessGradientNormSq_pos : 0 < sharpnessGradientNormSq) :
    balanceVariance progressiveSharpening sharpnessGradientNormSq < 0 := by
  unfold balanceVariance
  exact div_neg_of_neg_of_pos (by linarith) sharpnessGradientNormSq_pos

/-! ## Hilbert-space projected flow -/

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-- Increase in sharpness under the unprojected negative loss gradient. -/
def progressiveSharpening
    (lossGradient sharpnessGradient : State) : ℝ :=
  ⟪sharpnessGradient, -lossGradient⟫_ℝ

/-- The one-mode variance from equation (13). -/
def oneModeVariance
    (lossGradient sharpnessGradient : State) : ℝ :=
  balanceVariance
    (progressiveSharpening lossGradient sharpnessGradient)
    (‖sharpnessGradient‖ ^ 2)

/-- Equation (14), before substituting the balancing variance. -/
def penalizedFlowDirection
    (learningRate variance : ℝ)
    (lossGradient sharpnessGradient : State) : State :=
  -learningRate •
    (lossGradient + (variance / 2) • sharpnessGradient)

/-- The loss gradient with its sharpness-gradient component removed. -/
def projectedLossGradient
    (lossGradient sharpnessGradient : State) : State :=
  AndersonGainGeometry.depthOneOptimizedResidual
    lossGradient sharpnessGradient

/-- Equation (15): negative projected gradient flow. -/
def centralFlowDirection
    (learningRate : ℝ)
    (lossGradient sharpnessGradient : State) : State :=
  -learningRate •
    projectedLossGradient lossGradient sharpnessGradient

/-- The Hilbert-space projection is exactly the depth-one Anderson
least-squares residual. -/
theorem projectedLossGradient_eq
    (lossGradient sharpnessGradient : State) :
    projectedLossGradient lossGradient sharpnessGradient =
      lossGradient -
        (⟪sharpnessGradient, lossGradient⟫_ℝ /
          ‖sharpnessGradient‖ ^ 2) • sharpnessGradient := by
  rfl

/-- Substituting the unique balancing variance into equation (14) gives the
projected central flow in equation (15). -/
theorem penalizedFlow_eq_centralFlow
    (learningRate : ℝ)
    (lossGradient sharpnessGradient : State)
    (sharpnessGradient_ne_zero : sharpnessGradient ≠ 0) :
    penalizedFlowDirection learningRate
        (oneModeVariance lossGradient sharpnessGradient)
        lossGradient sharpnessGradient =
      centralFlowDirection learningRate
        lossGradient sharpnessGradient := by
  have normSq_ne_zero : ‖sharpnessGradient‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr sharpnessGradient_ne_zero)
  have coefficientEq :
      oneModeVariance lossGradient sharpnessGradient / 2 =
        -(AndersonGainGeometry.depthOneCoefficient
          lossGradient sharpnessGradient) := by
    simp only [oneModeVariance, balanceVariance, progressiveSharpening,
      inner_neg_right, AndersonGainGeometry.depthOneCoefficient]
    field_simp [normSq_ne_zero]
  rw [penalizedFlowDirection, centralFlowDirection, coefficientEq]
  simp only [projectedLossGradient,
    AndersonGainGeometry.depthOneOptimizedResidual]
  module

/-- The balancing one-mode variance is the unique variance that makes the
sharpness derivative vanish. -/
theorem oneModeVariance_balances_sharpness
    (learningRate : ℝ)
    (lossGradient sharpnessGradient : State)
    (learningRate_ne_zero : learningRate ≠ 0)
    (sharpnessGradient_ne_zero : sharpnessGradient ≠ 0) :
    sharpnessDrift learningRate
        (progressiveSharpening lossGradient sharpnessGradient)
        (‖sharpnessGradient‖ ^ 2)
        (oneModeVariance lossGradient sharpnessGradient) = 0 := by
  apply (sharpnessDrift_eq_zero_iff
    learningRate
    (progressiveSharpening lossGradient sharpnessGradient)
    (‖sharpnessGradient‖ ^ 2)
    (oneModeVariance lossGradient sharpnessGradient)
    learningRate_ne_zero
    (pow_ne_zero 2
      (norm_ne_zero_iff.mpr sharpnessGradient_ne_zero))).2
  rfl

/-- Equation (15) preserves sharpness to first order: the central-flow
direction is orthogonal to the sharpness gradient. -/
theorem inner_sharpnessGradient_centralFlow_eq_zero
    (learningRate : ℝ)
    (lossGradient sharpnessGradient : State)
    (sharpnessGradient_ne_zero : sharpnessGradient ≠ 0) :
    ⟪sharpnessGradient,
        centralFlowDirection learningRate
          lossGradient sharpnessGradient⟫_ℝ = 0 := by
  rw [centralFlowDirection, real_inner_smul_right]
  change
    -learningRate *
      ⟪sharpnessGradient,
        AndersonGainGeometry.depthOneOptimizedResidual
          lossGradient sharpnessGradient⟫_ℝ = 0
  rw [AndersonGainGeometry.inner_history_optimizedResidual_eq_zero
    lossGradient sharpnessGradient sharpnessGradient_ne_zero, mul_zero]

/-- Exact loss derivative along the one-mode central flow. -/
theorem inner_lossGradient_centralFlow_eq
    (learningRate : ℝ)
    (lossGradient sharpnessGradient : State) :
    ⟪lossGradient,
        centralFlowDirection learningRate
          lossGradient sharpnessGradient⟫_ℝ =
      -learningRate *
        (‖lossGradient‖ ^ 2 -
          ⟪sharpnessGradient, lossGradient⟫_ℝ ^ 2 /
            ‖sharpnessGradient‖ ^ 2) := by
  rw [centralFlowDirection, real_inner_smul_right,
    projectedLossGradient_eq, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm lossGradient sharpnessGradient]
  ring

/-- Cauchy--Schwarz appears here as the nonnegative amount of loss-gradient
energy left after removing the sharpness component. -/
theorem projectedLossGradient_budget_nonneg
    (lossGradient sharpnessGradient : State)
    (sharpnessGradient_ne_zero : sharpnessGradient ≠ 0) :
    0 ≤
      ‖lossGradient‖ ^ 2 -
        ⟪sharpnessGradient, lossGradient⟫_ℝ ^ 2 /
          ‖sharpnessGradient‖ ^ 2 := by
  rw [← AndersonGainGeometry.depthOneOptimizedResidual_norm_sq
    lossGradient sharpnessGradient sharpnessGradient_ne_zero]
  exact sq_nonneg _

/-- With nonnegative learning rate, the projected flow cannot increase the
loss to first order. -/
theorem inner_lossGradient_centralFlow_nonpos
    (learningRate : ℝ)
    (lossGradient sharpnessGradient : State)
    (learningRate_nonneg : 0 ≤ learningRate)
    (sharpnessGradient_ne_zero : sharpnessGradient ≠ 0) :
    ⟪lossGradient,
        centralFlowDirection learningRate
          lossGradient sharpnessGradient⟫_ℝ ≤ 0 := by
  rw [inner_lossGradient_centralFlow_eq
    learningRate lossGradient sharpnessGradient]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr learningRate_nonneg)
    (projectedLossGradient_budget_nonneg
      lossGradient sharpnessGradient sharpnessGradient_ne_zero)

/-- If loss and sharpness gradients are orthogonal, projection removes
nothing and central flow recovers ordinary negative gradient flow. -/
theorem centralFlow_eq_negativeGradient_of_orthogonal
    (learningRate : ℝ)
    (lossGradient sharpnessGradient : State)
    (orthogonal :
      ⟪sharpnessGradient, lossGradient⟫_ℝ = 0) :
    centralFlowDirection learningRate
        lossGradient sharpnessGradient =
      -learningRate • lossGradient := by
  simp [centralFlowDirection, projectedLossGradient_eq, orthogonal]

/-- Negative boundary: when the loss gradient is entirely parallel to a
nonzero sharpness gradient, the constrained flow stalls. -/
theorem centralFlow_eq_zero_of_lossGradient_eq_smul
    (learningRate coefficient : ℝ)
    (sharpnessGradient : State)
    (sharpnessGradient_ne_zero : sharpnessGradient ≠ 0)
    (lossGradient : State)
    (parallel : lossGradient = coefficient • sharpnessGradient) :
    centralFlowDirection learningRate
        lossGradient sharpnessGradient = 0 := by
  subst lossGradient
  rw [centralFlowDirection, projectedLossGradient]
  have normSq_ne_zero : ‖sharpnessGradient‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr sharpnessGradient_ne_zero)
  have coefficientEq :
      AndersonGainGeometry.depthOneCoefficient
          (coefficient • sharpnessGradient) sharpnessGradient =
        coefficient := by
    rw [AndersonGainGeometry.depthOneCoefficient,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [normSq_ne_zero]
  have optimizedEq :
      AndersonGainGeometry.depthOneOptimizedResidual
          (coefficient • sharpnessGradient) sharpnessGradient = 0 := by
    rw [AndersonGainGeometry.depthOneOptimizedResidual, coefficientEq]
    simp
  rw [optimizedEq, smul_zero]

/-! ## Concrete positive and negative fixtures -/

/-- A progressive unit force with unit sharpness-gradient norm is balanced by
variance two. -/
theorem unit_progressive_balance :
    balanceVariance 1 1 = 2 ∧ sharpnessDrift 1 1 1 2 = 0 := by
  norm_num [balanceVariance, sharpnessDrift]

/-- A regressive unit force would require variance `-2`, exposing the regime
boundary of the covariance interpretation. -/
theorem regressive_negative_variance :
    balanceVariance (-1) 1 = -2 := by
  norm_num [balanceVariance]

/-- In one dimension every nonzero sharpness gradient spans the full space,
so the projected flow has no remaining direction. -/
theorem scalar_parallel_stall :
    centralFlowDirection (State := ℝ) 1 3 2 = 0 := by
  norm_num [centralFlowDirection, projectedLossGradient_eq]

#print axioms sharpnessDrift_eq_zero_iff
#print axioms balanceVariance_pos_iff
#print axioms balanceVariance_neg_of_regressive
#print axioms penalizedFlow_eq_centralFlow
#print axioms oneModeVariance_balances_sharpness
#print axioms inner_sharpnessGradient_centralFlow_eq_zero
#print axioms inner_lossGradient_centralFlow_eq
#print axioms projectedLossGradient_budget_nonneg
#print axioms inner_lossGradient_centralFlow_nonpos
#print axioms centralFlow_eq_negativeGradient_of_orthogonal
#print axioms centralFlow_eq_zero_of_lossGradient_eq_smul
#print axioms unit_progressive_balance
#print axioms regressive_negative_variance
#print axioms scalar_parallel_stall

end

end CentralFlowProjection

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
