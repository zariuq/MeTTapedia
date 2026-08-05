import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.CoordinateRescue
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.EquilibratedEnergySaddles

/-!
# Exact trust-region core for a one-hidden-unit linear network

This file isolates the algebraic content of the one-MLP calculation in
Innocenti, Singh, and Buckley, *Understanding Predictive Coding as an Adaptive
Trust-Region Method* (arXiv:2305.18188; the workshop version uses
“Second-Order” in the title).  State equilibrium and the rescaled loss are
exact.  The paper's Equation 7 is exact only after choosing its local
quadratic Taylor model; that model and its solved stationarity equation are
formalized explicitly below.  The discarded higher-order remainder is
recorded as a scope boundary, not silently turned into an equality.

The local Hessian comparison is also scalar and exact.  It verifies the larger
negative-curvature magnitude used by the saddle-escape argument and the
strictly smaller residual curvature at nonzero-output minima.  It then imports
the sealed strict-origin certificate and the sealed counterexample to
unrestricted universal strictness.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Exact one-MLP equilibrium -/

/-- Ordinary half-squared loss of the scalar two-weight linear network. -/
noncomputable def oneMLPLoss
    (input target firstWeight secondWeight : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (target - secondWeight * firstWeight * input) ^ 2

/-- Predictive-coding free energy with one free hidden activity. -/
noncomputable def oneMLPFreeEnergy
    (input target firstWeight secondWeight hidden : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (hidden - firstWeight * input) ^ 2 +
    (1 / 2 : ℝ) * (target - secondWeight * hidden) ^ 2

/-- Exact hidden-state equilibrium. -/
noncomputable def oneMLPEquilibrium
    (input target firstWeight secondWeight : ℝ) : ℝ :=
  (firstWeight * input + secondWeight * target) /
    (1 + secondWeight ^ 2)

/-- State derivative of the one-MLP free energy. -/
noncomputable def oneMLPStateGradient
    (input target firstWeight secondWeight hidden : ℝ) : ℝ :=
  (1 + secondWeight ^ 2) * hidden -
    (firstWeight * input + secondWeight * target)

/-- Exact finite increment, exposing both the state gradient and positive
quadratic curvature. -/
theorem oneMLPFreeEnergy_increment_exact
    (input target firstWeight secondWeight hidden increment : ℝ) :
    oneMLPFreeEnergy input target firstWeight secondWeight (hidden + increment) -
        oneMLPFreeEnergy input target firstWeight secondWeight hidden =
      increment * oneMLPStateGradient input target firstWeight secondWeight hidden +
        (1 / 2 : ℝ) * (1 + secondWeight ^ 2) * increment ^ 2 := by
  simp [oneMLPFreeEnergy, oneMLPStateGradient]
  ring

/-- The closed-form activity exactly solves state stationarity. -/
theorem oneMLPStateGradient_at_equilibrium
    (input target firstWeight secondWeight : ℝ) :
    oneMLPStateGradient input target firstWeight secondWeight
      (oneMLPEquilibrium input target firstWeight secondWeight) = 0 := by
  have hden : 1 + secondWeight ^ 2 ≠ 0 := by positivity
  simp [oneMLPStateGradient, oneMLPEquilibrium]
  field_simp
  ring

/-- Equation 13 exactly: equilibrated free energy is ordinary loss divided by
the predictive variance `1 + secondWeight²`. -/
theorem oneMLPFreeEnergy_at_equilibrium_eq_rescaledLoss
    (input target firstWeight secondWeight : ℝ) :
    oneMLPFreeEnergy input target firstWeight secondWeight
        (oneMLPEquilibrium input target firstWeight secondWeight) =
      oneMLPLoss input target firstWeight secondWeight /
        (1 + secondWeight ^ 2) := by
  have hden : 1 + secondWeight ^ 2 ≠ 0 := by positivity
  simp [oneMLPFreeEnergy, oneMLPEquilibrium, oneMLPLoss]
  field_simp
  ring

/-! ## Equation 7 inside its declared quadratic model -/

/-- Solved shift of a scalar quadratic Taylor model. -/
noncomputable def quadraticStateShift
    (fisher stateLossGradient : ℝ) : ℝ :=
  -stateLossGradient / fisher

/-- The local model's stationarity equation is solved exactly. -/
theorem quadraticStateShift_solves_stationarity
    (fisher stateLossGradient : ℝ) (hfisher : fisher ≠ 0) :
    fisher * quadraticStateShift fisher stateLossGradient +
      stateLossGradient = 0 := by
  simp [quadraticStateShift]
  field_simp
  ring

/-- Weight gradient in the local model, written using the inferred state
displacement. -/
noncomputable def linearizedPCWeightGradient
    (backpropGradient stateJacobian displacement : ℝ) : ℝ :=
  backpropGradient - stateJacobian * displacement

/-- Exact Equation-7 algebra inside the local quadratic model: substituting
the solved state displacement adds the inverse-Fisher correction. -/
theorem linearizedPCWeightGradient_eq_inverseFisherCorrection
    (backpropGradient stateJacobian fisher stateLossGradient : ℝ) :
    linearizedPCWeightGradient backpropGradient stateJacobian
        (quadraticStateShift fisher stateLossGradient) =
      backpropGradient +
        stateJacobian * (stateLossGradient / fisher) := by
  simp [linearizedPCWeightGradient, quadraticStateShift]
  ring

/-- Approximation status is data rather than a proposition. -/
inductive TrustRegionClaimStatus
  | exactQuadraticIdentity
  | localTaylorApproximation
  deriving DecidableEq, Repr

structure TrustRegionBoundaryClaim where
  description : String
  status : TrustRegionClaimStatus
  deriving DecidableEq, Repr

/-- The omitted cubic Taylor remainder in the paper's Equation 5 remains an
explicit approximation boundary. -/
def equationSevenTaylorBoundary : TrustRegionBoundaryClaim where
  description := "Equation 7 outside the chosen local quadratic Taylor model"
  status := .localTaylorApproximation

theorem equationSevenTaylorBoundary_not_exact :
    equationSevenTaylorBoundary.status ≠ .exactQuadraticIdentity := by
  decide

/-! ## Local saddle-escape curvature -/

/-- Magnitude of the negative eigenvalue of the backpropagation Hessian at the
scalar origin. -/
noncomputable def backpropOriginEscapeMagnitude (input target : ℝ) : ℝ :=
  |input * target|

/-- Magnitude of the negative eigenvalue of the predictive-coding Hessian at
the scalar origin. -/
noncomputable def pcOriginEscapeMagnitude (input target : ℝ) : ℝ :=
  (target ^ 2 +
      Real.sqrt (target ^ 4 + 4 * (input * target) ^ 2)) / 2

/-- Positive eigenvalue of the predictive-coding Hessian at the scalar
origin.  This is the attracting curvature magnitude in Theorem A.3. -/
noncomputable def pcOriginAttractionMagnitude (input target : ℝ) : ℝ :=
  (-target ^ 2 +
      Real.sqrt (target ^ 4 + 4 * (input * target) ^ 2)) / 2

/-- The claimed backpropagation negative eigenvalue satisfies its exact
characteristic equation. -/
theorem backpropOrigin_negativeEigenvalue_characteristic
    (input target : ℝ) :
    (-backpropOriginEscapeMagnitude input target) ^ 2 -
      (input * target) ^ 2 = 0 := by
  unfold backpropOriginEscapeMagnitude
  rw [neg_sq, sq_abs]
  ring

/-- The claimed predictive-coding negative eigenvalue satisfies the exact
characteristic polynomial of the local Hessian
`[[0,-input*target],[-input*target,-target²]]`. -/
theorem pcOrigin_negativeEigenvalue_characteristic
    (input target : ℝ) :
    (-pcOriginEscapeMagnitude input target) ^ 2 +
        target ^ 2 * (-pcOriginEscapeMagnitude input target) -
      (input * target) ^ 2 = 0 := by
  have hrad : 0 ≤ target ^ 4 + 4 * (input * target) ^ 2 := by positivity
  have hsqrt := Real.sq_sqrt hrad
  simp only [pcOriginEscapeMagnitude]
  nlinarith

/-- A nonzero target makes the PC negative-curvature magnitude strictly larger
than BP's, the exact local comparison underlying the A.3 escape claim. -/
theorem pcOrigin_escapeMagnitude_strictly_larger
    (input target : ℝ) (htarget : target ≠ 0) :
    backpropOriginEscapeMagnitude input target <
      pcOriginEscapeMagnitude input target := by
  have habs : 0 ≤ 2 * |input * target| := by positivity
  have htargetSq : 0 < target ^ 2 := sq_pos_of_ne_zero htarget
  have hsqrt :
      2 * |input * target| <
        Real.sqrt (target ^ 4 + 4 * (input * target) ^ 2) := by
    rw [Real.lt_sqrt habs]
    rw [show (2 * |input * target|) ^ 2 =
        4 * (input * target) ^ 2 by
      rw [mul_pow, sq_abs]
      ring]
    nlinarith [sq_pos_of_pos htargetSq]
  simp only [backpropOriginEscapeMagnitude, pcOriginEscapeMagnitude]
  linarith

/-- Full non-degenerate curvature comparison behind Theorem A.3: PC is less
attracted to the origin along its positive eigendirection and more strongly
repelled along its negative eigendirection than BP. -/
theorem pcOrigin_full_curvature_comparison
    (input target : ℝ) (hinput : input ≠ 0) (htarget : target ≠ 0) :
    0 < pcOriginAttractionMagnitude input target ∧
      pcOriginAttractionMagnitude input target <
        backpropOriginEscapeMagnitude input target ∧
      backpropOriginEscapeMagnitude input target <
        pcOriginEscapeMagnitude input target := by
  have hproduct : input * target ≠ 0 := mul_ne_zero hinput htarget
  have habs : 0 < |input * target| := abs_pos.mpr hproduct
  have htargetSq : 0 < target ^ 2 := sq_pos_of_ne_zero htarget
  have hlower :
      target ^ 2 <
        Real.sqrt (target ^ 4 + 4 * (input * target) ^ 2) := by
    rw [Real.lt_sqrt (sq_nonneg target)]
    nlinarith [sq_pos_of_ne_zero hproduct]
  have hright : 0 < target ^ 2 + 2 * |input * target| := by positivity
  have hupper :
      Real.sqrt (target ^ 4 + 4 * (input * target) ^ 2) <
        target ^ 2 + 2 * |input * target| := by
    rw [Real.sqrt_lt' hright]
    nlinarith [sq_abs (input * target), mul_pos htargetSq habs]
  refine ⟨?_, ?_, pcOrigin_escapeMagnitude_strictly_larger
    input target htarget⟩
  · simp only [pcOriginAttractionMagnitude]
    linarith
  · simp only [pcOriginAttractionMagnitude, backpropOriginEscapeMagnitude]
    linarith

/-- Positive fixture for the strict saddle-escape comparison. -/
theorem unit_oneMLP_pc_escapeMagnitude :
    backpropOriginEscapeMagnitude 1 1 < pcOriginEscapeMagnitude 1 1 := by
  exact pcOrigin_escapeMagnitude_strictly_larger 1 1 (by norm_num)

/-- Negative boundary: at zero target the two curvature magnitudes coincide. -/
theorem zeroTarget_escapeMagnitudes_equal (input : ℝ) :
    backpropOriginEscapeMagnitude input 0 = pcOriginEscapeMagnitude input 0 := by
  simp [backpropOriginEscapeMagnitude, pcOriginEscapeMagnitude]

/-! ## Exact flatter-minimum residual curvature -/

/-- Residual-direction curvature of the equilibrated one-MLP energy relative
to the unit curvature of ordinary half-squared loss. -/
noncomputable def equilibratedResidualCurvature (secondWeight : ℝ) : ℝ :=
  1 / (1 + secondWeight ^ 2)

/-- Nonzero output weight strictly flattens the residual direction. -/
theorem equilibratedResidualCurvature_pos_lt_one
    (secondWeight : ℝ) (hsecond : secondWeight ≠ 0) :
    0 < equilibratedResidualCurvature secondWeight ∧
      equilibratedResidualCurvature secondWeight < 1 := by
  constructor
  · simp [equilibratedResidualCurvature]
    positivity
  · rw [equilibratedResidualCurvature, div_lt_one (by positivity)]
    nlinarith [sq_pos_of_ne_zero hsecond]

/-- Negative boundary: a zero output weight gives no flattening. -/
theorem equilibratedResidualCurvature_zeroWeight :
    equilibratedResidualCurvature 0 = 1 := by
  norm_num [equilibratedResidualCurvature]

/-! ## Exact Theorem A.4 positive Hessian eigenvalue -/

/-- The unique positive Hessian eigenvalue of the BP loss at the 1MLP minimum
`w₁ = target / (w₂ * input)`, as stated in Theorem A.4. -/
noncomputable def bpMinimumPositiveCurvature
    (input target secondWeight : ℝ) : ℝ :=
  (secondWeight ^ 4 * input ^ 2 + target ^ 2) / secondWeight ^ 2

/-- The unique positive Hessian eigenvalue of the equilibrated PC energy at
the same minimum. -/
noncomputable def pcMinimumPositiveCurvature
    (input target secondWeight : ℝ) : ℝ :=
  (secondWeight ^ 4 * input ^ 2 + target ^ 2) /
    (secondWeight ^ 2 * (1 + secondWeight ^ 2))

/-- Exact A.4 rescaling of the nonzero curvature eigenvalue. -/
theorem pcMinimumPositiveCurvature_eq_bp_div_predictiveVariance
    (input target secondWeight : ℝ) (hsecond : secondWeight ≠ 0) :
    pcMinimumPositiveCurvature input target secondWeight =
      bpMinimumPositiveCurvature input target secondWeight /
        (1 + secondWeight ^ 2) := by
  unfold pcMinimumPositiveCurvature bpMinimumPositiveCurvature
  field_simp [hsecond]

/-- Exact A.4 flattening theorem in its non-degenerate 1MLP regime: the PC
minimum has strictly smaller positive Hessian eigenvalue than the
corresponding BP minimum. -/
theorem pcMinimumPositiveCurvature_strictly_flatter
    (input target secondWeight : ℝ)
    (hinput : input ≠ 0) (hsecond : secondWeight ≠ 0) :
    0 < pcMinimumPositiveCurvature input target secondWeight ∧
      pcMinimumPositiveCurvature input target secondWeight <
        bpMinimumPositiveCurvature input target secondWeight := by
  have hsecondSq : 0 < secondWeight ^ 2 := sq_pos_of_ne_zero hsecond
  have hinputSq : 0 < input ^ 2 := sq_pos_of_ne_zero hinput
  have hsecondFourth : 0 < secondWeight ^ 4 := by positivity
  have hnumerator :
      0 < secondWeight ^ 4 * input ^ 2 + target ^ 2 := by
    nlinarith [mul_pos hsecondFourth hinputSq, sq_nonneg target]
  have hvariance : 1 < 1 + secondWeight ^ 2 := by linarith
  have hbp :
      0 < bpMinimumPositiveCurvature input target secondWeight := by
    exact div_pos hnumerator hsecondSq
  constructor
  · unfold pcMinimumPositiveCurvature
    exact div_pos hnumerator (mul_pos hsecondSq (by positivity))
  · rw [pcMinimumPositiveCurvature_eq_bp_div_predictiveVariance
      input target secondWeight hsecond]
    exact div_lt_self hbp hvariance

/-! ## Strict-saddle theorem and conjecture boundary -/

/-- Lift of the sealed strict-origin certificate. -/
theorem frontier_origin_hasStrictSaddleCertificate :
    HasStrictSaddleCertificate orthogonalDatasetEquilibratedEnergy (0, 0) :=
  orthogonalDataset_origin_hasStrictSaddleCertificate

/-- Scope status for the strict-origin result. -/
inductive DeepOriginClaimStatus
  | exactScalarTwoLayer
  | resolvedByMatrixLineRestriction
  deriving DecidableEq, Repr

structure DeepOriginBoundaryClaim where
  description : String
  status : DeepOriginClaimStatus
  deriving DecidableEq, Repr

/-- The formerly open deep-linear origin boundary, now marked as resolved by
the arbitrary-depth matrix line-restriction theorem family. -/
def generalDeepLinearOriginBoundary : DeepOriginBoundaryClaim where
  description :=
    "arbitrary-depth matrix PC origin theorem resolved by exact line restriction"
  status := .resolvedByMatrixLineRestriction

theorem generalDeepLinearOriginBoundary_resolved :
    generalDeepLinearOriginBoundary.status = .resolvedByMatrixLineRestriction := by
  decide

/-- Lift of the sealed counterexample to unrestricted universal strictness. -/
theorem frontier_universalStrictSaddle_counterexample :
    IsCriticalPoint orthogonalDatasetEquilibratedEnergy (1, 0) ∧
      HasTwoSidedSaddleCurves orthogonalDatasetEquilibratedEnergy (1, 0)
        (fun step => (1 - step, step))
        (fun step => (1 + step, step)) ∧
      (∀ direction,
        HasSecondDirectionalCurvatureAt orthogonalDatasetEquilibratedEnergy
          (1, 0) direction 0) ∧
      ¬ HasStrictSaddleCertificate orthogonalDatasetEquilibratedEnergy (1, 0) :=
  orthogonalDataset_universalStrictSaddleConjecture_counterexample

inductive ConjectureStatus
  | openUnderAdditionalHypotheses
  | refutedWithoutAdditionalHypotheses
  deriving DecidableEq, Repr

structure NamedConjecture where
  name : String
  status : ConjectureStatus
  deriving DecidableEq, Repr

/-- The literature conjecture is retained by name but explicitly marked as
refuted in its unrestricted form; this record carries no axiom or proof field. -/
def allEquilibratedSaddlesStrictConjecture : NamedConjecture where
  name := "all equilibrated predictive-coding saddles are strict"
  status := .refutedWithoutAdditionalHypotheses

theorem allEquilibratedSaddlesStrictConjecture_is_not_open_unrestricted :
    allEquilibratedSaddlesStrictConjecture.status ≠
      .openUnderAdditionalHypotheses := by
  decide

#print axioms pcOrigin_escapeMagnitude_strictly_larger
#print axioms pcOrigin_full_curvature_comparison
#print axioms pcMinimumPositiveCurvature_strictly_flatter
#print axioms frontier_origin_hasStrictSaddleCertificate
#print axioms frontier_universalStrictSaddle_counterexample

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
